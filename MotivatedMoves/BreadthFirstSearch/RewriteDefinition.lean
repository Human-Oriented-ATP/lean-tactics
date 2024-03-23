import MotivatedMoves.Moves.TreeRewriteDef
import MotivatedMoves.BreadthFirstSearch.Move

open Lean Elab Tactic Move MotivatedTree
  
def rewriteDefinitionMove : Move where 
  name := "Rewrite Definition"
  tactic position := do
    let (outer, inner) := splitPosition position
    workOnTreeDefEq (edit outer inner replaceByDef)
    let mkTree ← `(tactic | make_tree)
    evalTactic mkTree

@[aesop unsafe tactic (rule_sets [Move.BFS])]
def rewriteDefinitionMoveBFS := rewriteDefinitionMove.toBFSCapableTactic
