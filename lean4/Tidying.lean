import Lean

open Lean Expr Meta Elab Tactic

/-- Tidying consists mostly of instantiating instances in the types
of goals/hypotheses. For a single expression we use a custom reduce-/
def tidyingReduce : Expr → MetaM Expr := fun e =>
  (withTransparency .instances (reduce (skipTypes := false) e))

/-- Modifies a goal by tidying the type of the target -/
def metaTidyGoal : MVarId -> MetaM (MVarId) :=
  fun originalGoal => do
    let originalType ← originalGoal.getType
    let newType ← tidyingReduce originalType
    let newGoal ← mkFreshExprMVar newType
    originalGoal.assign newGoal
    return newGoal.mvarId!

/-- Modifies all declarations (e.g. hypotheses) associated with a goal
-/
def metaTidyDeclarations : MVarId -> MetaM (MVarId) :=
  fun goal => do
    let mut goal' := goal
    for decl in ← getLCtx do
      if decl.isImplementationDetail then
        continue
      let newType ← tidyingReduce decl.type
      goal' ← goal'.replaceLocalDeclDefEq decl.fvarId newType
    return goal'

/-- Tidy the target of the main goal -/
elab "tidy_target" : tactic =>
  withMainContext do
    liftMetaTactic fun goal => do
      return [← metaTidyGoal goal]

/-- Tidy the declarations of the main goal -/
elab "tidy_declarations" : tactic =>
  withMainContext do
    liftMetaTactic fun goal => do
      return [← metaTidyDeclarations goal]

/-- Tidy the target and declarations of the main goal-/
elab "tidy_all" : tactic =>
  withMainContext do
    liftMetaTactic fun goal => do
      return [← metaTidyDeclarations (← metaTidyGoal goal)]

/-- Tidies all targets and declarations everywhere -/
elab "tidy_everything" : tactic => do
  evalTactic (← `(tactic| all_goals tidy_all))
