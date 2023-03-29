import Lean

open Classical
open Lean Elab Tactic

elab "skolemize_hypothesis" h:Parser.Tactic.locationHyp : tactic => do
  evalTactic (← `(tactic| simp only [skolem] at $h))

elab "skolemize_goal" : tactic => do
  evalTactic (← `(tactic| simp only [skolem]))

elab "skolemize_all" : tactic => do
  evalTactic (← `(tactic| simp only [skolem] at *))

elab "skolemize_everything" : tactic => do
  evalTactic (← `(tactic| all_goals skolemize_all))
