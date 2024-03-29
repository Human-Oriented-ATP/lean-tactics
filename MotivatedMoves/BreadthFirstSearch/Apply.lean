import MotivatedMoves.Moves.TreeApply
import MotivatedMoves.BreadthFirstSearch.Move

open Lean Elab Tactic Move MotivatedTree
  
def applyMove : Move2 where 
  name := "Apply"
  tactic := fun (position1, position2) => do
    let (outer1, inner1) := splitPosition position1
    let (outer2, inner2) := splitPosition position2
    workOnTree (applyBound outer1 outer2 inner1 inner2 true treeApply true)

@[aesop unsafe tactic (rule_sets [Move.BFS])]
def applyMoveBFS := applyMove.toBFSCapableTactic
