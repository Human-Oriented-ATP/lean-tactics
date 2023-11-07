import MotivatedMoves.BreadthFirstSearch.RewriteDefinition 

namespace test

def x : Nat := 0

example : x = 0 := by 
  -- make_tree
  -- tree_rewrite_def [2, 1, 0]
  -- rfl
  bfs_motivated_moves

end test
