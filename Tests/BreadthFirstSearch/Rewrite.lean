import MotivatedMoves.BreadthFirstSearch.Rewrite

variables (a b : Nat)

example (h : a = b) : a = b := by 
  bfs_motivated_moves

example (h1 : a = b) (h2 : b = c) : a = c := by 
  bfs_motivated_moves
