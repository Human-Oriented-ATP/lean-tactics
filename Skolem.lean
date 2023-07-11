import Lean
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Contrapose

open Classical
open Lean Elab Meta Tactic Expr

theorem skolem' {α : Type u} {b : α → Type v} {p : ∀ x, b x → Prop} : (∀ x, ∃ y, p x y) ↔
 ∃ (f : ∀ x, b x), ∀ x, p x (f x) := skolem

protected def Nonempty.forallelim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : ∀ (x : α), p) : p :=
  match h₁ with
  | intro a => h₂ a

example [Nonempty α] : (∀ (x : α), P) → P := sorry

-- to push out forall quantifiers (just a restricted version of `forall_swap`)
lemma push_out_forall {α : Type u} {P : Prop} {Q : α → Prop} : (P → ∀ x, Q x) ↔ ∀ x, P → Q x := forall_swap

-- to push out existential quantifiers
lemma push_out_exists {α : Type u} [h₁ : Nonempty α] {P : Prop} {Q : α → Prop} : (P → (∃ x, Q x)) ↔ ∃ x, P → Q x := by
  refine ⟨?_, fun ⟨x, hx⟩ hP => ⟨x, hx hP⟩⟩
  intro h
  contrapose! h 
  rw [forall_and] at h
  exact ⟨Nonempty.elim h₁ h.1, h.2⟩

elab "move_quantifiers_goal" : tactic => do
  evalTactic (← `(tactic| simp only [push_out_forall, push_out_exists]))

elab "move_quantifiers_hyp" h:Parser.Tactic.locationHyp : tactic => do
  evalTactic (← `(tactic| simp only [push_out_forall, push_out_exists] at $h))

elab "move_quantifiers_all" : tactic => do
  evalTactic (← `(tactic| simp only [push_out_forall, push_out_exists] at *))

/-- Applies recursive skolemization in a given hypothesis -/
elab "skolemize_hypothesis" h:Parser.Tactic.locationHyp : tactic => do
  evalTactic (← `(tactic| simp only [skolem'] at $h))

/-- Applies recursive skolemization to the current goal -/
elab "skolemize_goal" : tactic => do
  evalTactic (← `(tactic| simp only [skolem']))

/-- Applies recursive skolemization to all hypotheses and current goal
-/
elab "skolemize_all" : tactic => do
  evalTactic (← `(tactic| simp only [skolem'] at *))

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


-- never want to see this version of skolemization
example {P : Prop} {Q : Nat → Prop} : (P → ∃ x, Q x) ↔ ∃ f : _ → _, ∀ (x : P), Q (f x) := by
  rw [skolem]

example {P : Prop} {α : Type u} [Nonempty α] {Q : α → Prop}: (P → ∃ x : α, Q x) ↔ ∃ x : α, P → Q x := by 
  sorry

lemma test_case (h : 5 = 5 → ∀ (n : Nat), n = 5 → ∃ (m : Nat), m = n) : 3 = 3 → ∀ (n : Nat), n = 5 := by
  move_quantifiers_all
  skolemize_hypothesis h
  sorry

/- Skolemization procedure
  1. Push all of the quantifiers (both `∀` and `∃` outwards) as much as possible in both goals and hypotheses.
  This is handled by the `move_quantifiers_all` tactic.
  2. Introduce all universally quantified variables in the goal and instantiate the rest with metavariables 
  3. Skolemize all hypotheses. This is done using the tactic `skolemize_hypothesis` for a singular hypothesis.
-/

syntax (name := introduce) "introduce" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

@[tactic introduce] def evalIntro' : Tactic := fun stx => do
  match stx with
  | `(tactic| introduce)                   => introStep none `_
  | `(tactic| introduce $h:ident)          => introStep h h.getId
  | `(tactic| introduce _%$tk)             => introStep tk `_
  /- Type ascription -/
  | `(tactic| introduce ($h:ident : $type:term)) => introStep h h.getId type
  /- We use `@h` at the match-discriminant to disable the implicit lambda feature -/
  | `(tactic| introduce $pat:term)         => evalTactic (← `(tactic| introduce h; match @h with | $pat:term => ?_; try clear h))
  | `(tactic| introduce $h:term $hs:term*) => evalTactic (← `(tactic| introduce $h:term; introduce $hs:term*))
  | _ => throwUnsupportedSyntax
where
  introStep (ref : Option Syntax) (n : Name) (typeStx? : Option Syntax := none) : TacticM Unit := do
    let fvarId ← liftMetaTacticAux fun mvarId => do
      let (fvarId, mvarId) ← mvarId.intro n
      pure (fvarId, [mvarId])
    if let some typeStx := typeStx? then
      withMainContext do
        let type ← Term.withSynthesize (mayPostpone := true) <| Term.elabType typeStx
        let fvar := mkFVar fvarId
        let fvarType ← inferType fvar
        unless (← isDefEqGuarded type fvarType) do
          throwError "type mismatch at `intro {fvar}`{← mkHasTypeButIsExpectedMsg fvarType type}"
        liftMetaTactic fun mvarId => return [← mvarId.replaceLocalDeclDefEq fvarId type]
    if let some stx := ref then
      withMainContext do
        Term.addLocalVarInfo stx (mkFVar fvarId)

example (x : Nat): ∀ x : Nat, x = x := by
  introduce x
  sorry