import Lean
import Qq

open Lean Qq Elab Term Tactic Meta

theorem imp_subst {P Q Q' : Prop} (imp : Q → Q') (h : P → Q) : P → Q' :=
  fun p ↦ imp (h p)

partial def generateApplication {A B : Q(Prop)} (h : Q($A → $B)) (target : Q(Prop)) : MetaM ((e : Q(Prop)) × Q($e → $target)) := do
  match ← isDefEqQ B target (u := .succ .zero) with
  | .defEq _prf => return ⟨A, h⟩
  | .notDefEq =>
    match target with
    | ~q((($P) : Prop) → $Q) =>
      let ⟨Q', prf⟩ ← generateApplication h Q
      return ⟨q($P → $Q'), q(imp_subst $prf)⟩
    -- | ~q($P ∨ $Q) => return target
    -- | ~q($P ∧ $Q) => return target
    -- | ~q(¬$P) => return target
    -- | ~q($P ↔ $Q) => return target
    -- | ~q(∃ x : $α, $P x) => return target
    -- | ~q(∀ x : $α, (($P) : $α → Prop) $x) => sorry
    | _ => return ⟨target, q(id (α := $target))⟩

elab "deep_apply" f:term : tactic => withMainContext do
  let fvarId ← getFVarId f
  let ⟨.zero, hypType, h⟩ ← inferTypeQ (.fvar fvarId) | throwError "Expected hypothesis to be a proposition."
  match hypType with
  | ~q((($P) : Prop) → $Q) =>
    let ⟨.zero, target, mvar⟩ ← inferTypeQ (.mvar (← getMainGoal)) | throwError "Expected goal to be a proposition."
    let ⟨newTarget, prf⟩ ← generateApplication (A := P) (B := Q) h target
    let e ← mkFreshExprMVarQ newTarget
    mvar.mvarId!.assign q($prf $e)
    replaceMainGoal [e.mvarId!]
  | _ => throwError "Expected hypothesis to be an implication."

example {P Q R : Prop} (h₁ : P → R) (h₂ : R → Q) : P → Q := by
  deep_apply h₂
  exact h₁
