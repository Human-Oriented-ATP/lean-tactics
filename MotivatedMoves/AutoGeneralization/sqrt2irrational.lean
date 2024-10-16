import Mathlib.Data.Real.Irrational
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic
import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic4000

theorem sqrt2_irrational {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a^2 ≠ 2 * b^2 := by
  intro h
  have hfin_b : multiplicity.Finite 2 b := by
    simp [@multiplicity.finite_int_iff, hb]
  have hfin_rhs : multiplicity.Finite (2 : ℤ) (2 * b^2) := by
    simp [@multiplicity.finite_int_iff, hb]
  have hfin_lhs : multiplicity.Finite (2 : ℤ) (a^2) := by rwa [h]
  have hfin_a : multiplicity.Finite 2 a := by
    simp [@multiplicity.finite_int_iff, ha]
  -- suffices 2 * (multiplicity 2 a).get hfin_a % 2 ≠ (1 + 2 * (multiplicity 2 b).get hfin_b) % 2 from sorry
  have : (multiplicity 2 (a ^ 2)).get hfin_lhs % 2 = (multiplicity 2 (2 * b ^ 2)).get hfin_rhs % 2 := by
    congr
  conv at this =>
    lhs
    rw [multiplicity.pow' Int.prime_two hfin_a]
  conv at this =>
    rhs
    rw [multiplicity.mul' Int.prime_two, multiplicity.pow' Int.prime_two hfin_b]
    rw [multiplicity.get_multiplicity_self (multiplicity.finite_of_finite_mul_right hfin_rhs)]
  simp at this
