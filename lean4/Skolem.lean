import Lean

open Classical
open Lean Elab Meta Tactic Expr

#check skolem

/-- Applies recursive skolemization in a given hypothesis -/
elab "skolemize_hypothesis" h:Parser.Tactic.locationHyp : tactic => do
  evalTactic (← `(tactic| simp only [skolem] at $h))

/-- Applies recursive skolemization to the current goal -/
elab "skolemize_goal" : tactic => do
  evalTactic (← `(tactic| simp only [skolem]))

/-- Applies recursive skolemization to all hypotheses and current goal
-/
elab "skolemize_all" : tactic => do
  evalTactic (← `(tactic| simp only [skolem] at *))

/-- Applies recursive skolemization everywhere (all goals affected) -/
elab "skolemize_everything" : tactic => do
  evalTactic (← `(tactic| all_goals skolemize_all))

/-- Root skolemization only applies skolemization once, in the case
that the goal is of the form ∀x, ∃y, P x y. -/
elab "root_skolemize_goal" : tactic => do
  evalTactic (← `(tactic| apply skolem.mpr))

-- def skolemForwards := skolem.mp

/-- Root skolemization only applies skolemization once, in the case
that the hypothesis is of the form ∀x, ∃y, P x y. -/
elab "root_skolemize_hypothesis" h:term : tactic => do
  withMainContext do
    let hExpr ← elabTerm h none
    match hExpr with
    | fvar fvarId =>
      liftMetaTactic fun goal => do
        -- let originalProp ←
        -- let newProp := .app
        let proof := const ``Classical.skolem
        let assert ← goal.replaceLocalDecl fvarId newProp proof
        let goal' ← return goal
        return [goal']
    | _ => logError m!"{h} is not a hypothesis"
