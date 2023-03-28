import Lean

open Lean Expr Meta Elab Tactic

-- Don't worry about this secret, it is used to test the import system
def secret : Nat := 10

def tidyingReduce : Expr → MetaM Expr := fun e =>
  (withTransparency .instances (reduce (skipTypes := false) e))

def metaTidyGoal : MVarId -> MetaM (MVarId) :=
  fun originalGoal => do
    let originalType ← originalGoal.getType
    let newType ← tidyingReduce originalType
    let newGoal ← mkFreshExprMVar newType
    originalGoal.assign newGoal
    return newGoal.mvarId!

def metaTidyDeclarations : MVarId -> MetaM (MVarId) :=
  fun goal => do
    let mut goal' := goal
    for decl in ← getLCtx do
      if decl.isImplementationDetail then
        continue
      let newType ← tidyingReduce decl.type
      goal' ← goal'.changeLocalDecl decl.fvarId newType
      -- goal' ← goal'.assert decl.userName newType decl.toExpr
      -- (_, goal') ← goal'.intro1P
    return goal'

elab "tidy_goal" : tactic => 
  withMainContext do
    liftMetaTactic fun goal => do
      return [← metaTidyGoal goal]

elab "trace_state" : tactic => do
  let goal ← getMainGoal
  IO.println "Current goal:"
  IO.println (← goal.getType)
  goal.withContext do
    for decl in ← getLCtx do
      IO.println s!"Hypothesis {decl.userName} of type {decl.type}"

elab "tidy_everything" : tactic =>
  withMainContext do
    let goal ← getMainGoal 
    goal.withContext do
      liftMetaTactic fun originalGoal => do
        return [← metaTidyDeclarations (← metaTidyGoal originalGoal)]

#check LocalDecl.applyFVarSubst
#check FVarSubst
#check LocalContext
#check MVarId.changeLocalDecl
