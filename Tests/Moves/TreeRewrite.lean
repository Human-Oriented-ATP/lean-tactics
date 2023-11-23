import MotivatedMoves.Moves.TreeRewrite
import Mathlib.Analysis.SpecialFunctions.Exp



example (p q : Prop) : (p ∧ (p → (p ↔ q))) → (q → False) → False := by
  make_tree
  tree_rewrite [0,1,1,2,1] [1,0,0,2]
  sorry

example : (∀ n : Nat, n = n+1) → (∃ m : Nat, m = m+1) → True := by
  make_tree
  tree_rewrite [0,1,2] [1,0,1,2,0,1]
  sorry

example : (∀ n l : Nat, n = l+n) → ∃ y : Nat, {x : Nat | x + 1 = y} = {3} := by
  make_tree
  tree_rewrite [0,1,1,2] [1,1,2,0,1,1,1,0,1]
  sorry

elab "hii" e:term : tactic => do
  let e ← Lean.Elab.Tactic.elabTerm e none
  let e ← Tree.DiscrTree.mkDTExpr e
  Lean.logInfo m! "{e}, {e.etaFlatten}"
example := by
  hii (fun x a c => (a:Nat) + ?y)
#check OfNat.ofNat
#exit
example : 1 + (3:ℤ) = a + a + a := by
try_lib_rewrite [2,1]

example (a : α → β → β → δ) : (fun x y z : β => a b c z) = (fun x y z => a b c d) := by
try_lib_rewrite [2,1]

example (a b c : Int) : a + b + c = a + (b + c) := by
  try_lib_rewrite [2,0,1]

open BigOperators
open Lean Tree DiscrTree in
def librarySearchRewrite (goalPos' : List Nat) (tree : Expr) : MetaM (Array (Array (Name × AssocList SubExpr.Pos Widget.DiffTag × String) × Nat)) := do
  let discrTrees ← getLibraryLemmas
  let (goalOuterPosition, goalPos) := splitPosition goalPos'
  let results := (← getSubExprUnify discrTrees.2.rewrite tree goalOuterPosition goalPos) ++ (← getSubExprUnify discrTrees.1.rewrite tree goalOuterPosition goalPos)

  let results ← filterLibraryResults results fun {name, treePos, pos, ..} => do
    _ ← applyUnbound name (fun hyp _goalPath => return (← makeTreePath treePos hyp, treePos, pos)) goalOuterPosition goalPos treeRewrite tree

  return results.map $ Bifunctor.fst $ Array.map fun {name, treePos, pos, diffs} => (name, diffs, s! "lib_rewrite {printPosition treePos pos} {name} {goalPos'}")
open Lean Tree Meta Elab Tactic DiscrTree
elab "try_lib_rewrite" goalPos:treePos : tactic => do
  let goalPos := getPosition goalPos
  let tree := (← getMainDecl).type
  logLibrarySearch (← Tree.librarySearchRewrite goalPos tree)
example (N : ℕ) : ∑ n in Finset.range N, n  = N * (N - 1) / 2 := by
  try_lib_rewrite [2,0,1]

example (N : ℕ) : ∑ n in Finset.range N, (a + n)  = N * (N - 1) / 2 := by
  try_lib_rewrite [2,0,1]