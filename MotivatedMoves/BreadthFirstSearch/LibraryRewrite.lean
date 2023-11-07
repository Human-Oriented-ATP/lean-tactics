import MotivatedMoves.Moves.TreeRewrite
import MotivatedMoves.BreadthFirstSearch.Move

open Lean Elab Tactic Move Tree
  
def bestLibraryResult (position : List Nat) : TacticM Name := do
  let searchResult ← librarySearchRewrite position (← getMainTarget)
  pure `Nat

def libraryRewriteMove : Move (Array Nat) where 
  name := "Library Rewrite"
  tactic := fun position => do
    let bestLibraryResult ← bestLibraryResult position
    let (outer, inner) := splitPosition position
    workOnTree (applyUnbound bestLibraryResult (getRewritePos (.inr true)) outer inner treeRewrite)
    
@[aesop unsafe tactic (rule_sets [Move.BFS])]
def rewriteMoveBFS := libraryRewriteMove.toBFSCapableTactic
