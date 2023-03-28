import Lean

open Lean Elab Tactic Meta

/- A possible alternative to the built in trace_state tactic -/
elab "my_trace_state" : tactic => do
  for goal in ← getGoals do
    IO.println s!"Goal:{← instantiateMVars (← goal.getType)}"
    goal.withContext do
      for decl in ← getLCtx do
        if decl.isImplementationDetail then
          continue
        IO.println s!"Hypothesis {decl.userName} of type {decl.type}"
