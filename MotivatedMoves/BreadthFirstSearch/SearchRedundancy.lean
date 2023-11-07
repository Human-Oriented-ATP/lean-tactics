import MotivatedMoves.Moves.TreeSearch
import MotivatedMoves.BreadthFirstSearch.Move 

open Lean Elab Tactic Move 

def SearchRedundancyMove : Move Unit where
  name := "Search Redundancy"
  tactic := fun _ => do 
    evalTactic (← `(tactic| tree_search))

@[aesop unsafe tactic (rule_sets [Move.BFS])]
def searchRedundancyMoveBFS := SearchRedundancyMove.toBFSCapableTactic
