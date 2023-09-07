import TreeApply

namespace Tree

open Lean Meta

abbrev RewriteInfo := Expr × Expr × Expr × Expr

def rewriteUnify (fvars : Array Expr) (side target : Expr) (metaIntro : MetaM (Array Expr)) (proofM : MetaM' (Expr × Expr)) : MetaM' RewriteInfo := do
  let target := target.instantiateRev fvars
  let mvars ← metaIntro
  if (← isDefEq side target)
    then
      for mvar in mvars do
        _ ← elimMVarDeps fvars mvar
      let lctx ← getLCtx
      let (newSide, proof) ← proofM

      let n := fvars.size
      let motive_core := n.fold (.bvar · |> mkApp ·) (.bvar n)
      let newSide := newSide.abstract fvars

      let proof ← fvars.foldrM (fun fvar proof => mkAppM ``funext #[lctx.mkLambda #[fvar] proof]) proof
      let type := lctx.mkForall fvars (← inferType newSide)

      return (motive_core, newSide, proof, type)
  else
    throwError m!"subexpression {target} : {← inferType target} does not match side {side} : {← inferType side}"

def recurseToPosition (side target : Expr) (metaIntro : MetaM (Array Expr)) (proofM : MetaM' (Expr × Expr)) (pos : List Nat) : MetaM' RewriteInfo :=
  
  let rec visit (fvars : Array Expr) : List Nat → Expr → MetaM' RewriteInfo
    | xs   , .mdata d b        => do let (e, e', z) ← visit fvars xs b; return (.mdata d e, .mdata d e', z)

    | []   , e                 => rewriteUnify fvars side e metaIntro proofM
    
    | 0::xs, .app f a          => do let (e, e', z) ← visit fvars xs f; return (.app e a, .app e' a, z)
    | 1::xs, .app f a          => do let (e, e', z) ← visit fvars xs a; return (.app f e, .app f e', z)

    | 0::xs, .proj n i b       => do let (e, e', z) ← visit fvars xs b; return (.proj n i e, .proj n i e', z)

    | 0::xs, .letE n t v b c   => do let (e, e', z) ← visit fvars xs t; return (.letE n e v b c, .letE n e' v b c, z)
    | 1::xs, .letE n t v b c   => do let (e, e', z) ← visit fvars xs v; return (.letE n t e b c, .letE n t e' b c, z)
    | 2::xs, .letE n t v b c   =>
      withLocalDeclD n (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.letE n t v e c, .letE n t v e' c, z)
                                                      
    | 0::xs, .lam n t b bi     => do let (e, e', z) ← visit fvars xs t; return (.lam n e b bi, .lam n e' b bi, z)
    | 1::xs, .lam n t b bi     =>
      withLocalDecl n bi (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.lam n t e bi, .lam n t e' bi, z)

    | 0::xs, .forallE n t b bi => do let (e, e', z) ← visit fvars xs t; return (.forallE n e b bi, .forallE n e' b bi, z)
    | 1::xs, .forallE n t b bi =>
      withLocalDecl n bi (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.forallE n t e bi, .forallE n t e' bi, z)

    | list, e                  => throwError m!"could not find subexpression {list} in '{e}'"
      
  visit #[] pos target

lemma substitute  {α : Sort u} {a b : α} (motive : α → Prop) (h₁ : Eq a b) : motive b → motive a :=
  Eq.subst h₁.symm

lemma substitute' {α : Sort u} {a b : α} (motive : α → Prop) (h₁ : Eq a b) : motive a → motive b :=
  Eq.subst h₁

def treeRewrite (symm : Bool) (eq : Expr) (metaIntro : MetaM (Array Expr)) (proofM : MetaM' (Expr × Expr)) (pos : List Nat) (pol : Bool) (target : Expr) : MetaM' TreeProof :=
  let cont (lhs rhs : Expr) (proofM : MetaM' (Expr × Expr)) :=
    let cont (side : Expr) (proofM : MetaM' (Expr × Expr)) : MetaM' TreeProof := do
    
      let (motive_core, newSide, proof, type) ← recurseToPosition side target metaIntro proofM pos
      let motive := Expr.lam `_a type motive_core .default
      let proof ← mkAppM (if pol != symm then ``substitute else ``substitute') #[motive, proof]
      return { newTree := newSide, proof}

    if symm
    then cont rhs <| Bifunctor.fst (·.appFn!.appArg!) <$> proofM
    else cont lhs <| Bifunctor.fst (·.appArg!) <$> proofM

  match eq.iff? with
  | some (lhs, rhs) => cont lhs rhs do
      let (.app (.app _ a) b, h) ← proofM | throwError ""
      return (mkApp3 (mkConst ``Eq [.succ .zero]) (.sort .zero) a b, (mkApp3 (mkConst ``propext) a b h))
  | none =>
  match eq.eq? with
  | some (_, lhs, rhs) => cont lhs rhs proofM
  | none => throwError m!"equality or iff proof expected{indentExpr eq}"
    


open Elab Tactic

syntax (name := tree_rewrite) "tree_rewrite" treePos treePos : tactic

@[tactic tree_rewrite]
def evalTreeRewrite : Tactic := fun stx => do
  let hypPos := get_positions stx[1]
  let goalPos := get_positions stx[2]
  workOnTree (applyBound hypPos goalPos · true (treeRewrite false))

syntax (name := tree_rewrite_rev) "tree_rewrite_rev" treePos treePos : tactic

@[tactic tree_rewrite_rev]
def evalTreeRewriteRev : Tactic := fun stx => do
  let hypPos := get_positions stx[1]
  let goalPos := get_positions stx[2]
  workOnTree (applyBound hypPos goalPos · true (treeRewrite true))





example (p q : Prop) : (p ∧ (p → (p ↔ q))) → (q → False) → False := by
  make_tree
  tree_rewrite_rev [0,1,1,1] [1,0,1,0,1]
  sorry

example : (∀ n : Nat, n = n+1) → (∃ m : Nat, m = m+1) → True := by
  make_tree
  tree_rewrite [0,1,1,1] [1,0,1,1,1,0,1]
  sorry


example : (∀ n l : Nat, n = l+n) → ∃ y : Nat, {x : Nat | x + 1 = y} = {3} := by
  make_tree
  tree_rewrite [0,1,1,1,1,1] [1,1,1,0,1,1,1,0,1]
  sorry