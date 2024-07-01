import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic3000

open Real

-- Uncomment below to hide proofs of "let" statements in the LeanInfoview
set_option pp.showLetValues false
-- set_option pp.explicit false
-- set_option pp.all true
-- set_option profiler true
theorem irr'  : ¬∃x : ℚ, x*x = (2:ℚ) := by
    intro h
    obtain ⟨x, hx⟩ := h
    have ab := (Iff.mp Rat.eq_iff_mul_eq_mul) hx
    simp at ab
    have ab_copr := x.reduced

    rw [Rat.mul_self_num] at ab

    rw [Rat.mul_self_den] at ab


    have num_sq_even : 2 ∣ x.num * x.num := by
      apply (Iff.mpr dvd_iff_exists_eq_mul_right)
      use ↑(x.den *x.den)

    have num_even : 2 ∣ x.num := by
      have := Iff.mp (Prime.dvd_mul (Int.prime_two)) num_sq_even
      cases this with
      | inl h => exact h
      | inr h => exact h

    have num_abs_even : 2 ∣ (Int.natAbs x.num) := by
      have mp := (Iff.mpr $ dvd_abs 2 x.num) num_even
      rw [Int.abs_eq_natAbs] at mp
      norm_cast at *

    have num_is_2k : ∃ k,  x.num = 2*k := by
      apply (Iff.mp dvd_iff_exists_eq_mul_right)
      exact num_even

    obtain ⟨k, hk⟩ := num_is_2k
    rw [hk] at ab
    rw [mul_assoc] at ab
    simp [mul_left_cancel] at ab
    rw [mul_comm k, mul_assoc] at ab

    have den_sq_even : 2 ∣ ((x.den * x.den) : ℤ) := by
      apply (Iff.mpr dvd_iff_exists_eq_mul_right)
      use (k*k)
      apply Eq.symm
      exact ab


    have den_even : 2 ∣ x.den := by
      have := Iff.mp (Prime.dvd_mul (Int.prime_two)) den_sq_even
      norm_cast at this
      cases this with
      | inl h => exact h
      | inr h => exact h

    unfold Nat.Coprime at ab_copr

    have two_dvd_gcd : 2 ∣ gcd (Int.natAbs x.num) x.den  := by
      have := Iff.mpr (dvd_gcd_iff 2  (Int.natAbs x.num) x.den)
      apply this
      constructor

      exact num_abs_even
      exact den_even

    rw [gcd_eq_nat_gcd] at two_dvd_gcd

    simp [ab_copr] at two_dvd_gcd


theorem irr : ¬∃x : ℚ, x*x = (2:ℚ) := by
  by_contra h
  obtain ⟨x, hx⟩ := h
  have ab := (Iff.mp Rat.eq_iff_mul_eq_mul) hx
  simp at ab
  have ab_copr := x.reduced

  have asq : (x*x).num = x.num*x.num := by rw [Rat.mul_self_num]

  have bsq : (x*x).den = x.den*x.den := by rw [Rat.mul_self_den]

  rw [ab] at asq

  have num_sq_even : 2 ∣ x.num * x.num := by
    apply (Iff.mpr dvd_iff_exists_eq_mul_right)
    use ↑(x *x).den
    rw [asq]

  have num_even : 2 ∣ x.num := by
    have := Iff.mp (Prime.dvd_mul (Int.prime_two)) num_sq_even
    cases this with
    | inl h => exact h
    | inr h => exact h

  have num_abs_even : 2 ∣ (Int.natAbs x.num) := by
    have mp := (Iff.mpr $ dvd_abs 2 x.num) num_even
    rw [Int.abs_eq_natAbs] at mp
    norm_cast at *

  have num_is_2k : ∃ k,  x.num = 2*k := by
    apply (Iff.mp dvd_iff_exists_eq_mul_right)
    exact num_even

  obtain ⟨k, hk⟩ := num_is_2k
  rw [hk, bsq] at asq
  rw [mul_assoc] at asq
  simp [mul_left_cancel] at asq
  rw [mul_comm k, mul_assoc] at asq

  have den_sq_even : 2 ∣ ((x.den * x.den) : ℤ) := by
    apply (Iff.mpr dvd_iff_exists_eq_mul_right)
    use (k*k)

  have den_even : 2 ∣ x.den := by
    have := Iff.mp (Prime.dvd_mul (Int.prime_two)) den_sq_even
    norm_cast at this
    cases this with
    | inl h => exact h
    | inr h => exact h

  unfold Nat.Coprime at ab_copr

  have two_dvd_gcd : 2 ∣ gcd (Int.natAbs x.num) x.den  := by
    have := Iff.mpr (dvd_gcd_iff 2  (Int.natAbs x.num) x.den)
    apply this
    constructor

    exact num_abs_even
    exact den_even

  rw [gcd_eq_nat_gcd] at two_dvd_gcd

  simp [ab_copr] at two_dvd_gcd


#check irr'
#check irr
