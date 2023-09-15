import TreeApply

namespace Tree

open Lean Meta Elab.Tactic




elab "tree_induction" goalPos:treePos : tactic => do
  let goalPos := getPosition goalPos
  workOnTreeAt goalPos fun pos pol tree => do
  unless pos == [] do
    throwError m! "cannot apply induction in a subexpression: position {pos} in {indentExpr tree}"
  match tree with
  | imp_pattern domain _
  | forall_pattern _n _u domain _ =>
    if pol
    then do
    let domain ← whnfD domain
    matchConst domain.getAppFn
      (fun _ => throwError m! "type is not an inductive type {indentExpr domain}")
      (fun cinfo _ => do
        let .inductInfo val := cinfo | throwError m! "expected an inductive type {indentExpr domain}"
        if val.all.length != 1 then
          throwError "'induction' move does not support mutually inductive types, the eliminator '{mkRecName val.name}' has multiple motives"
        if val.isNested then
          throwError "'induction' move does not support nested inductive types, the eliminator '{mkRecName val.name}' has multiple motives"
        
        let init l := l.take (l.length - 1)
        let recName := .str val.name (if val.name == `Nat then "recAux" else "rec")
        applyUnbound recName (fun recType _ => (init (getPath recType),[])) [] treeApply tree
      )
    else
      throwError m! "cannot do induction in negative position"
        

  | _ => throwError m! "can't apply induction"

-- inductive ind (α β : Type) (x y : Nat) where
-- | two : ind α β x 0 
-- | one : ind α β x y → ind α β x (y + 1)
-- #check Vector

-- inductive Vector : Type u → Nat → Type (u + 1) where
-- | cons : α →  (Vector α n) → Vector α (n+1)
-- -- | nil : Vector α 0

-- #check Vector.cons

-- inductive Vector' : Nat → Type u → Type (u + 1) where
-- | cons : α → Vector' n α → Vector' (n+1) α 
-- | nil : Vector' 0 α 

-- #check Vector.rec
-- #check Vector'.rec
-- #check Eq.rec
-- #eval show MetaM _ from do
--   match (← getEnv).find? `Tree.Vector with
--     -- n throwError "")
--     | some (.inductInfo val) => return (val.numIndices, val.numParams)
--     | _ => throwError ""
--   -- throwError "nono"

-- example : p ∨ q → q ∨ p := by
--   make_tree
--   tree_induction []
#check Nat.recAux
example : ∀ n : ℕ, n = (n * (n - 1) / 2) := by
  make_tree
  tree_induction []
  simp
  lib_apply trivial [0,1]
  sorry

universe u v w
variable {α : Type imax u v w}