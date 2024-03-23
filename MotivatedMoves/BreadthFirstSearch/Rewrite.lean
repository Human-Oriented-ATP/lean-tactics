import MotivatedMoves.Moves.TreeRewrite
import MotivatedMoves.BreadthFirstSearch.Move

open Lean Elab Tactic Move MotivatedTree
  
def rewriteMove : Move2 where 
  name := "Rewrite"
  tactic := fun (position1, position2) => do
    let (outer1, inner1) := splitPosition position1
    let (outer2, inner2) := splitPosition position2
    workOnTree (applyBound outer1 outer2 inner1 inner2 true treeRewrite)

@[aesop unsafe tactic (rule_sets [Move.BFS])]
def rewriteMoveBFS := rewriteMove.toBFSCapableTactic
