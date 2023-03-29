import Lean

open Classical
open Lean Elab Tactic

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
