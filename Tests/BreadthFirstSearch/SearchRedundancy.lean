import MotivatedMoves.BreadthFirstSearch.SearchRedundancy

example : True := by 
  bfs_motivated_moves

example : ∀_ : Type, True := by 
  bfs_motivated_moves

example : True ∧ True := by 
  bfs_motivated_moves
  
example (hyp : h) : h := by 
  bfs_motivated_moves
