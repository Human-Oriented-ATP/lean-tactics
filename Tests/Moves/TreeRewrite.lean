import MotivatedMoves.Moves.TreeRewrite

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