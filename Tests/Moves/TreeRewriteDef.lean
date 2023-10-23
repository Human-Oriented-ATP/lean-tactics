import MotivatedMoves.Moves.TreeRewriteDef

example : ∀ n:Nat, n + n = 2*n := by
  make_tree
  tree_rewrite_def [1,2,0,1]
  tree_rewrite_def [1,2,0,1]
  sorry

example : ∀ n:Nat, Prod.fst (n,n) = n := by
  make_tree
  tree_rewrite_def [1,2,0,1]
  sorry

example : (fun x => x) 1 = 1 := by
  tree_rewrite_def [2,0,1]
  rfl