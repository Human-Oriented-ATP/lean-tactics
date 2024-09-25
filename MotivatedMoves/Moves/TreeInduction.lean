import MotivatedMoves.Moves.TreeApply

namespace MotivatedTree

open Lean Meta Elab.Tactic

def getInductionPos (hyp : Expr) (_ : MetaM Bool) : MetaM (Expr × OuterPosition × InnerPosition) := do
  let hypTree ← makeTree hyp
  let path := findOuterPosition hypTree
  return (← makeTreePath path hyp, path.take (path.length - 1), [])

elab "tree_induction" pos:treePos : tactic => do
  let (treePos, pos) := getOuterInnerPosition pos
  (workOnTreeAt treePos fun pol tree => do
  unless pos == [] do
    throwError m! "cannot apply induction in a subexpression: position {pos} in {indentExpr tree}"
  match tree with
    | imp_pattern domain _
    | forall_pattern _ _ domain _ =>
      unless pol do
        throwError m! "cannot do induction in negative position"
      let domain ← whnfD domain
      matchConst domain.getAppFn
        (fun _ => throwError m! "expected an inductive type, not {indentExpr domain}")
        fun cinfo _ => do
          let .inductInfo val := cinfo | throwError m! "expected an inductive type, not {indentExpr domain}"
          if val.all.length != 1 then
            throwError "'induction' move does not support mutually inductive types, the eliminator '{mkRecName val.name}' has multiple motives"
          if val.isNested then
            throwError "'induction' move does not support nested inductive types, the eliminator '{mkRecName val.name}' has multiple motives"

          let recName : Name := .str val.name (if val.name == `Nat then "recAux" else "rec")
          applyUnbound recName getInductionPos [] [] treeApply tree
    | _ => throwError m! "cannot apply induction at {tree}")
  workOnTreeDefEq makeTree


def or_elim₁ : (p ∨ q) → r ↔ (p → r) ∧ (¬ p → q → r) := by
  by_cases h:p <;> simp [h]
def or_elim₂ : (p ∨ q) → r ↔ (p → ¬q → r) ∧ (q → r) := by
  by_cases h:q <;> simp [h]
def or_elim₃ : (p ∨ q) → r ↔ (p → r) ∧ (q → r) := by
  by_cases h:p <;> simp [h]
  intro _ _
  assumption
private def or_diffs : AssocList SubExpr.Pos Widget.DiffTag :=
  AssocList.nil.cons (.ofArray #[1,1,1,0,1]) .willChange |>.cons (.ofArray #[1,1,1,1]) .wasChanged

def nat_induct {p : ℕ → Prop} : (∀ n, p n) ↔ p 0 ∧ ∀ n, p n → p (n+1) := by
  apply Iff.intro
  · intro h
    simp [h]
  · intro h
    exact Nat.rec h.1 h.2
def nat_induct_strong {p : ℕ → Prop} : (∀ n, p n) ↔ ∀ n, (∀ m, m < n → p m) → p n := by
  apply Iff.intro
  · intro h
    simp [h]
  · intro h n
    exact Nat.strongInductionOn n h
private def nat_diffs : AssocList SubExpr.Pos Widget.DiffTag :=
  AssocList.nil.cons (.ofArray #[1,0,1]) .willChange |>.cons (.ofArray #[1,1]) .wasChanged

def custom_inductors : HashMap Name (Array LibraryLemma) :=
  HashMap.empty.insert ``Or #[
  {name := ``or_elim₁, treePos := [1,1,1], pos := [0,1], diffs := or_diffs},
  {name := ``or_elim₂, treePos := [1,1,1], pos := [0,1], diffs := or_diffs},
  {name := ``or_elim₃, treePos := [1,1,1], pos := [0,1], diffs := or_diffs}]
  |>.insert ``Nat #[
  {name := ``nat_induct,        treePos := [1], pos := [0,1], diffs := nat_diffs},
  {name := ``nat_induct_strong, treePos := [1], pos := [0,1], diffs := nat_diffs}
  ]

def librarySearchInduction (goalPos : List ℕ) (tree : Expr) : MetaM (Array (Name × AssocList SubExpr.Pos Widget.DiffTag × String)) := do
  let (goalOuterPosition, []) := splitPosition goalPos | return #[]
  MotivatedTree.withTreeSubexpr tree goalOuterPosition [] fun _ e => do
  match e with
    | imp_pattern domain _
    | forall_pattern _ _ domain _ =>
      let domain ← whnfD domain
      let .const name _ := domain.getAppFn | return #[]
      let some lemmas := custom_inductors.find? name | return #[]
      return lemmas.map fun {name, treePos, pos, diffs} => (name, diffs,
        s! "lib_rewrite {printPosition treePos pos} {name} {goalPos}")
    | _ => return #[]
