import MotivatedMoves.Moves.TreeContradiction 

example : (¬ p → q) → (¬ p → q) := by
  make_tree
  tree_contrapose [1,0] [1,1]
  tree_apply [0,1] [1,0,1]
  tree_push_neg [0]
  tree_apply [0] [1]