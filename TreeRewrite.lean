import TreeApply

namespace Tree

open Lean Meta

abbrev RewriteInfo := Expr × Expr × Expr × Expr

def rewriteUnify (fVars : Array Expr) (side target : Expr) (introMeta : MetaM Unit) (proofM : MetaM' (Expr × Expr)) : MetaM' RewriteInfo := do
  let target := target.instantiateRev fVars
  introMeta
  if (← isDefEq side target)
    then
      let (newSide, proof) ← proofM
      let proof ← fVars.foldrM (fun fvar proof => do mkAppM ``funext #[← mkLambdaFVars #[fvar] proof]) proof
      let type ← mkForallFVars fVars (← inferType newSide)

      let newSide := newSide.abstract fVars

      let n := fVars.size
      let motive_core := n.fold (.bvar · |> mkApp ·) (.bvar n)
      logInfo m!"{motive_core}"
      return (motive_core, newSide, proof, type)
  else
    throwError m!"subexpression {target} : {← inferType target} does not match side {side} : {← inferType side}"

def recurseToPosition (side target : Expr) (introMeta : MetaM Unit) (proofM : MetaM' (Expr × Expr)) (pos : List Nat) : MetaM' RewriteInfo :=
  
  let rec visit (fVars : Array Expr) : List Nat → Expr → MetaM' RewriteInfo
    | list, .mdata d b         => do let (e, e', z) ← visit fVars list b; return (.mdata d e, .mdata d e', z)

    | [], e => rewriteUnify fVars side e introMeta proofM
    
    | 0::xs, .app f a          => do let (e, e', z) ← visit fVars xs f; return (.app e a, .app e' a, z)
    | 1::xs, .app f a          => do let (e, e', z) ← visit fVars xs a; return (.app f e, .app f e', z)

    | 0::xs, .proj n i b       => do let (e, e', z) ← visit fVars xs b; return (.proj n i e, .proj n i e', z)

    | 0::xs, .letE n t v b c   => do let (e, e', z) ← visit fVars xs t; return (.letE n e v b c, .letE n e' v b c, z)
    | 1::xs, .letE n t v b c   => do let (e, e', z) ← visit fVars xs v; return (.letE n t e b c, .letE n t e' b c, z)
    | 2::xs, .letE n t v b c   =>
      withLocalDeclD n (t.instantiateRev fVars) fun fvar => do
        let (e, e', z) ← visit (fVars.push fvar) xs b
        return (.letE n t v e c, .letE n t v e' c, z)
                                                      
    | 0::xs, .lam n t b bi     => do let (e, e', z) ← visit fVars xs t; return (.lam n e b bi, .lam n e' b bi, z)
    | 1::xs, .lam n t b bi     =>
      withLocalDecl n bi (t.instantiateRev fVars) fun fvar => do
        let (e, e', z) ← visit (fVars.push fvar) xs b
        return (.lam n t e bi, .lam n t e' bi, z)

    | 0::xs, .forallE n t b bi => do let (e, e', z) ← visit fVars xs t; return (.forallE n e b bi, .forallE n e' b bi, z)
    | 1::xs, .forallE n t b bi =>
      withLocalDecl n bi (t.instantiateRev fVars) fun fvar => do
        let (e, e', z) ← visit (fVars.push fvar) xs b
        return (.forallE n t e bi, .forallE n t e' bi, z)

    | list, e                  => throwError m!"could not find subexpression {list} in '{e}'"
      
  visit #[] pos target

lemma substitute  {α : Sort u} {a b : α} (motive : α → Prop) (h₁ : Eq a b) : motive b → motive a :=
  Eq.subst h₁.symm

lemma substitute' {α : Sort u} {a b : α} (motive : α → Prop) (h₁ : Eq a b) : motive a → motive b :=
  Eq.subst h₁

def treeRewrite (symm : Bool) (eq : Expr) (introMeta : MetaM Unit) (proofM : MetaM' (Expr × Expr)) (pos : List Nat) (pol : Bool) (target : Expr) : MetaM' TreeProof :=
  let cont (lhs rhs : Expr) (proofM : MetaM' (Expr × Expr)) :=
    let cont (side : Expr) (proofM : MetaM' (Expr × Expr)) : MetaM' TreeProof := do
    
      let (motive_core, newSide, proof, type) ← recurseToPosition side target introMeta proofM pos
      logInfo m!"{motive_core}, {newSide}, {proof}, {type}"
      let motive := Expr.lam `_a type motive_core .default
      unless (← isTypeCorrect motive) do
        throwError m!"motive is not type correct{indentExpr motive}"
      let proof ← mkAppM (if pol != symm then ``substitute else ``substitute') #[motive, proof]
      pure { newTree := newSide, proof}

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
  workOnTree (applyBound hypPos goalPos · false (treeRewrite true))





example (p q : Prop) : (p ∧ (p → (p ↔ q))) → (q → False) → False := by
  make_tree
  tree_rewrite_rev [0,1,1,1] [1,0,1,0,1]
  sorry

example : (∀ n : Nat, n = n+1) → (∃ m : Nat, m = m+1) → True := by
  make_tree
  tree_rewrite [0,1,1,1] [1,0,1,1,1,0,1]
  sorry