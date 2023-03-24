import Lean

open Lean Expr Meta Elab Tactic

-- Don't worry about this secret, it is used to test the import system
def secret : Nat := 1

def tidyingReduce : Expr → MetaM Expr := fun e =>
  (withTransparency .instances (reduce (skipTypes := false) e))

elab "tidy_goal" : tactic => 
  withMainContext do
    liftMetaTactic fun originalGoal => do
      let originalType ← originalGoal.getType
      let newType ← tidyingReduce originalType
      let newGoal ← mkFreshExprMVar newType
      originalGoal.assign newGoal
      return [newGoal.mvarId!]

elab "trace_goal" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    IO.println "Current goal:"
    IO.println (← goal.getType)
