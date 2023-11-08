import MotivatedMoves.BreadthFirstSearch.RewriteDefinition
import MotivatedMoves.BreadthFirstSearch.SearchRedundancy
import MotivatedMoves.BreadthFirstSearch.Apply
import MotivatedMoves.BreadthFirstSearch.Rewrite

set_option trace.aesop.tree true
-- set_option trace.aesop.ruleSet true

example : True := by 
  bfs_motivated_moves


def f (x : Nat) : Prop := match x with 
  | 0 => True 
  | _ => False

example : f 0 := by 
  bfs_motivated_moves

example : f 0 ∨ f 1 := by 
  make_tree
  bfs_motivated_moves

example (h : f 0 = False) : f 0 = False := by 
  bfs_motivated_moves

def g : Prop → Prop := id

example : g (f 0) := by 
  bfs_motivated_moves

def h (x : Nat) : Nat := x^2 + 1

example (x : Nat) : f (h x) = False := by
  bfs_motivated_moves
