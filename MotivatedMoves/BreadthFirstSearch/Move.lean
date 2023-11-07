import Aesop
import MotivatedMoves.BreadthFirstSearch.UnsoundExhaustion 

open Lean Elab Tactic

-- Assumption: Always have one subgoal 

namespace Move

abbrev Position := List Nat 

structure Move (MoveArguments : Type u) where
  name : String
  tactic : List Nat → TacticM Unit
  -- validArguments? : Expr → Option (Array MoveArguments)

def Move.toBFSCapableTactic (m : Move α) : TacticM Unit := do
  exhaustParametricTacticOnAllPositions m.tactic 

structure Move2 (MoveArguments : Type u) where
  name : String
  tactic : (List Nat × List Nat) → TacticM Unit
  -- validArguments? : Expr → Option (Array MoveArguments)

def Move2.toBFSCapableTactic (m : Move2 α) : TacticM Unit := do
  exhaustParametricTacticOnAllPositions2 m.tactic 

declare_aesop_rule_sets [Move.BFS]

elab "bfs_motivated_moves" : tactic => do
  evalTactic (← `(tactic| aesop (rule_sets [Move.BFS, -default])
                                (options := {strategy := .breadthFirst 
                                             maxRuleApplications := 5000})
                                (simp_options := {enabled := false})))
