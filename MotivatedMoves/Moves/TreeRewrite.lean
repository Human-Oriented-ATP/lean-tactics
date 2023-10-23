import MotivatedMoves.Moves.TreeApply

namespace Tree

open Lean Meta

abbrev RewriteInfo := Expr × Expr × Expr × Expr

def rewriteUnify (fvars : Array Expr) (side target : Expr) (hypContext : HypothesisContext) : MetaM' RewriteInfo := do
  let target := target.instantiateRev fvars
  let {metaIntro, instMetaIntro, hypProofM} := hypContext
  let mvars ← metaIntro
  let instMVars ← instMetaIntro
  if (← isDefEq side target)
    then
      synthMetaInstances instMVars
      for mvar in mvars do
        _ ← elimMVarDeps fvars mvar

      let (newSide, proof) ← hypProofM
      let lctx ← getLCtx

      let n := fvars.size
      let motive_core := n.fold (.bvar · |> mkApp ·) (.bvar n)

      let proof ← fvars.foldrM (fun fvar proof => mkAppM ``funext #[lctx.mkLambda #[fvar] proof]) proof
      let type := lctx.mkForall fvars (← inferType newSide)
      let newSide := newSide.abstract fvars

      return (motive_core, newSide, proof, type)
  else
    throwError m!"subexpression {target} : {← inferType target} does not match side {side} : {← inferType side}"

private def recurseToPosition (side target : Expr) (hypContext : HypothesisContext) (pos : Pos) : MetaM' RewriteInfo :=
  
  let rec visit (fvars : Array Expr) : Pos → Expr → MetaM' RewriteInfo
    | xs   , .mdata d b        => do let (e, e', z) ← visit fvars xs b; return (.mdata d e, .mdata d e', z)

    | []   , e                 => rewriteUnify fvars side e hypContext
    
    | 0::xs, .app f a          => do let (e, e', z) ← visit fvars xs f; return (.app e a, .app e' a, z)
    | 1::xs, .app f a          => do let (e, e', z) ← visit fvars xs a; return (.app f e, .app f e', z)

    | 0::xs, .proj n i b       => do let (e, e', z) ← visit fvars xs b; return (.proj n i e, .proj n i e', z)

    | 0::xs, .letE n t v b d   => do let (e, e', z) ← visit fvars xs t; return (.letE n e v b d, .letE n e' v b d, z)
    | 1::xs, .letE n t v b d   => do let (e, e', z) ← visit fvars xs v; return (.letE n t e b d, .letE n t e' b d, z)
    | 2::xs, .letE n t v b d   =>
      withLocalDeclD n (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.letE n t v e d, .letE n t v e' d, z)
                                                      
    | 0::xs, .lam n t b bi     => do let (e, e', z) ← visit fvars xs t; return (.lam n e b bi, .lam n e' b bi, z)
    | 1::xs, .lam n t b bi     =>
      withLocalDeclD n (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.lam n t e bi, .lam n t e' bi, z)

    | 0::xs, .forallE n t b bi => do let (e, e', z) ← visit fvars xs t; return (.forallE n e b bi, .forallE n e' b bi, z)
    | 1::xs, .forallE n t b bi =>
      withLocalDeclD n (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.forallE n t e bi, .forallE n t e' bi, z)

    | list, e                  => throwError m!"could not find subexpression {list} in '{e}'"
      
  visit #[] pos target

lemma substitute  {α : Sort u} {a b : α} (motive : α → Prop) (h₁ : Eq a b) : motive b → motive a :=
  Eq.subst h₁.symm

lemma substitute' {α : Sort u} {a b : α} (motive : α → Prop) (h₁ : Eq a b) : motive a → motive b :=
  Eq.subst h₁

def treeRewrite (hypContext : HypothesisContext) (eq target : Expr) (pol : Bool) (hypTreePos : TreePos) (hypPos goalPos : Pos)
  : MetaM' TreeProof := do
  unless hypTreePos == [] do
    throwError m! "cannot rewrite using a subexpression: subtree {hypTreePos} in {eq}"
  let cont (lhs rhs : Expr) (hypProofM : MetaM' (Expr × Expr)) :=
    let cont (symm : Bool) (side : Expr) (hypProofM : MetaM' (Expr × Expr)) : MetaM' TreeProof := do
    
      let (motive_core, newSide, proof, type) ← recurseToPosition side target {hypContext with hypProofM} goalPos
      let motive := Expr.lam `_a type motive_core .default
      let proof ← mkAppM (if pol != symm then ``substitute else ``substitute') #[motive, proof]
      return { newTree := newSide, proof}

    match hypPos with
    | [1] => cont true rhs <| Bifunctor.fst (·.appFn!.appArg!) <$> hypProofM
    | []
    | [0,1] => cont false lhs <| Bifunctor.fst (·.appArg!) <$> hypProofM
    | _ => throwError m! "cannot rewrite with position {hypPos} in {eq}"

  match eq.iff? with
  | some (lhs, rhs) => cont lhs rhs (do
      let (.app (.app _ a) b, h) ← hypContext.hypProofM | throwError ""
      return (mkApp3 (mkConst ``Eq [.succ .zero]) (.sort .zero) a b, (mkApp3 (mkConst ``propext) a b h)))
  | none =>
  match eq.eq? with
  | some (_, lhs, rhs) => cont lhs rhs hypContext.hypProofM
  | none => throwError m!"equality or iff proof expected{indentExpr eq}"
    


open Elab.Tactic

elab "tree_rewrite" hypPos:treePos goalPos:treePos : tactic => do
  let (hypTreePos, hypPos) := getSplitPosition hypPos
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  workOnTree (applyBound hypTreePos goalTreePos hypPos goalPos true treeRewrite)

elab "tree_rewrite'" hypPos:treePos goalPos:treePos : tactic => do
  let (hypTreePos, hypPos) := getSplitPosition hypPos
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  workOnTree (applyBound hypTreePos goalTreePos hypPos goalPos false treeRewrite)

def getRewritePos (pos : TreePos × Pos ⊕ Bool) (hyp : Expr) (_ : MetaM Bool) : MetaM (Expr × TreePos × Pos) := do
  let hypTree ← makeTree hyp
  
  let (treePos, pos) := match pos with
    | .inl pos => pos
    | .inr rev? => 
      let treePos := findTreePos hypTree
      (treePos, (if rev? then [1] else [0,1]))
  return (← makeTreePath treePos hyp, treePos, pos)


elab "lib_rewrite" hypPos:(treePos)? hypName:ident goalPos:treePos : tactic => do
  let hypName ← getIdWithInfo hypName
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  let hypPos := hypPos.elim (.inr false) (.inl ∘ getSplitPosition)
  workOnTree (applyUnbound hypName (getRewritePos hypPos) goalTreePos goalPos treeRewrite)

elab "lib_rewrite_rev" hypName:ident goalPos:treePos : tactic => do
  let hypName ← getIdWithInfo hypName
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  workOnTree (applyUnbound hypName (getRewritePos (.inr true)) goalTreePos goalPos treeRewrite)

open DiscrTree in
def librarySearchRewrite (goalPos' : List Nat) (tree : Expr) : MetaM (Array (Array (Name × AssocList SubExpr.Pos Widget.DiffTag × String) × Nat)) := do
  let discrTrees ← getLibraryLemmas
  let (goalTreePos, goalPos) := splitPosition goalPos'
  let results := (← getSubExprUnify discrTrees.2.rewrite tree goalTreePos goalPos) ++ (← getSubExprUnify discrTrees.1.rewrite tree goalTreePos goalPos)

  let results ← filterLibraryResults results fun {name, treePos, pos, ..} => do
    try
      _ ← applyUnbound name (fun hyp _goalPath => return (← makeTreePath treePos hyp, treePos, pos)) goalTreePos goalPos treeRewrite tree
      return true
    catch _ =>
      return false

  return results.map $ Bifunctor.fst $ Array.map fun {name, treePos, pos, diffs} => (name, diffs, s! "lib_rewrite {printPosition treePos pos} {name} {goalPos'}")

elab "try_lib_rewrite" goalPos:treePos : tactic => do
  let goalPos := getPosition goalPos
  let tree := (← getMainDecl).type
  logLibrarySearch (← librarySearchRewrite goalPos tree)
