import Lean

open Classical
open Lean Elab Meta Tactic Expr

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

-- Helper definitions for use in the hypothesis root skolemization tactic
@[reducible] def skolem1.{u, v} {α : Sort u} {b : α → Sort v} {p : (x : α) → b x → Prop} :=
  ∀ x : α, ∃ y : b x, p x y

@[reducible] def skolem2.{u, v} {α : Sort u} {b : α → Sort v} {p : (x : α) → b x → Prop} :=
  ∃ f : (x : α) → b x, ∀ x : α, p x (f x)

def skolemEquality.{u, v}
  {α : Sort u} {b : α → Sort v} {p : (x : α) → b x → Prop} :=
  propext (@skolem.{u, v} (α : Sort u) (b : α → Sort v) (p : (x : α) → b x → Prop))

/-- Root skolemization only applies skolemization once, in the case
that the hypothesis is of the form ∀x, ∃y, P x y. -/
elab "root_skolemize_hypothesis" h:term : tactic => do
  withMainContext do
    let hExpr ← elabTerm h none
    match hExpr with
    | fvar fvarId =>
      liftMetaTactic fun goal => do
        let originalProp ← inferType hExpr
        let u ← mkFreshLevelMVar
        let v ← mkFreshLevelMVar
        let a ← mkFreshExprMVar (sort u)
        let b ← mkFreshExprMVar none
        let p ← mkFreshExprMVar none
        let metaOriginalProp := mkApp3 (const ``skolem1 [u, v]) a b p
        if ← isDefEq metaOriginalProp originalProp then
          let newProp ← withTransparency .reducible (reduce (skipTypes:= false)
            (mkApp3 (const ``skolem2 [u, v]) a b p))
          let proof := mkApp3 (const ``skolemEquality [u, v]) a b p
          let assertAfterResult ← goal.replaceLocalDecl fvarId newProp proof
          return [assertAfterResult.mvarId]
        else logError (m!"Error in root_skolemize_hypothesis: {h} " ++
                        m!"is not of the form ∀ x, ∃ y, p x y")
          return [goal]
    | _ => logError m!"Error in root_skolemize_hypothesis: {h} is not a hypothesis"
