import Lean
import Mathlib.Tactic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic
open Autogeneralize Classical Real

set_option trace.TypecheckingErrors true
set_option trace.AntiUnify true
set_option trace.ProofPrinting true

@[simp]
theorem all_equiv_pred_true_iff {q : Prop} : (∀ {p}, (p ↔ q) → p) ↔ q := by
  constructor
  · intro h
    have hq := h (p := q) Iff.rfl
    assumption
  · intro hq
    intro p hpq
    rw [hpq]
    assumption

example : Irrational (sqrt 2) := by
  let sqrt_irrat : Irrational (sqrt 17) := by {
    apply Nat.Prime.irrational_sqrt
    rw [← Nat.properDivisors_eq_singleton_one_iff_prime]
    decide
    -- rfl
  }
  autogeneralize (17:ℕ) in sqrt_irrat
  simp at sqrt_irrat.Gen
  specialize sqrt_irrat.Gen 2 rfl
  assumption
