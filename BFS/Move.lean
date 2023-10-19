import Lean 
import Aesop 

open Lean Elab Tactic 

-- library search is different because we have two scenarios
-- automatic: try first n results
-- interactive: choose result

-- How to deal with multiple subgoals? → currently: Not accepted, everything stays in one expression

namespace Move 

structure Move (MoveArguments : Type u) where 
  name : String
  tactic : Array SubExpr.Pos → MoveArguments → TacticM Unit
  validArguments? : Expr → Option (Array (Array (SubExpr.Pos) × MoveArguments))

def Move.toBFSCapableTactic (m : Move α) : TacticM Unit := do
  let target ← getMainTarget
  match m.validArguments? target with 
  | none => pure ()
  | some validArguments =>
    for (positions, argument) in validArguments do 
      m.tactic positions argument

-- want something like 
-- @[Add_to_BFS_ruleset]
-- before any move declaration

-- How to add such a move to Aesop? 

declare_aesop_rule_sets [Move.BFS]

