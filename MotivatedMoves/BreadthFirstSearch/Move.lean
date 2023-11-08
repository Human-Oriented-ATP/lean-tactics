import Aesop
import MotivatedMoves.BreadthFirstSearch.UnsoundExhaustion 

open Lean Elab Tactic

-- Assumption: Always have one subgoal 

namespace Move

structure Move where
  name : String
  tactic : List Nat → TacticM Unit

def Move.toBFSCapableTactic (m : Move) : TacticM Unit := do
  exhaustParametricTacticOnAllPositions m.tactic 

structure Move2 where
  name : String
  tactic : (List Nat × List Nat) → TacticM Unit

def Move2.toBFSCapableTactic (m : Move2) : TacticM Unit := do
  exhaustParametricTacticOnAllPositions2 m.tactic 

declare_aesop_rule_sets [Move.BFS]

macro "bfs_motivated_moves" : tactic =>  
  `(tactic| aesop (rule_sets [Move.BFS, -default])
                  (options := {strategy := .breadthFirst, maxRuleApplications := 5000})
                  (simp_options := {enabled := false}))
