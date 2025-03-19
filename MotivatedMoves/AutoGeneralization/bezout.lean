import Lean
import Mathlib.Tactic

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic
open Autogeneralize Classical

set_option trace.TypecheckingErrors true
set_option trace.ProofPrinting true

def isGCD (g a b : ℤ) : Prop := g ∣ a ∧ g ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g)
-- notation g " is GCD[" a ", " b "]" => isGCD g a b

theorem Int.emod_natAbs_lt_of_nonzero (a : ℤ) {b : ℤ} (hbAbs : b.natAbs ≠ 0)  : (a % b).natAbs < b.natAbs := by
  have hb : b ≠ 0 := by exact natAbs_ne_zero.mp hbAbs

  by_cases b_sign : b > 0
  refine natAbs_lt_natAbs_of_nonneg_of_lt ?_ ?_
  exact emod_nonneg a hb
  exact emod_lt_of_pos a b_sign

  simp at b_sign
  have b_neg : b < 0 := by exact lt_of_le_of_ne b_sign hb
  have negb_pos : -b > 0 := by exact Int.neg_pos_of_neg b_neg
  rw [← Int.emod_neg]
  rw [← natAbs_neg b]
  clear b_sign
  refine natAbs_lt_natAbs_of_nonneg_of_lt ?_ ?_
  rw [Int.emod_neg]
  exact emod_nonneg a hb
  exact emod_lt_of_pos a negb_pos

/-- Bézout's identity states that for any two integers a and b, there exist integers x and y such that their greatest common divisor g can be expressed as a linear combination ax + by = g -/
theorem bezout_identity : ∀ (x y : ℤ), y ≠ 0 → ∃ (h k : ℤ), isGCD (h * x + k * y) x y := by
  intros x y y_neq_0

  -- Consider the set A = {hx + ky | x,y ∈ ℤ}
  let A := {z : ℤ | ∃ h k : ℤ, z = h * x + k * y}
  -- Consider the set B = {|z| | z ∈ A, |z| ≠ 0} of non-zero absolute values
  have A_add : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A := by
    rintro a ⟨h, k, a_eq⟩ b ⟨h', k', b_eq⟩
    use (discharger := skip) (h + h'), (k + k')
    rw [a_eq, b_eq]
    rw [Int.add_assoc, Int.add_left_comm (k * y) _ _, ← Int.add_assoc, ← Int.add_mul, ← Int.add_mul]
  have A_mul : ∀ a ∈ A, ∀ z : ℤ, z * a ∈ A := by
    rintro a ⟨h, k, a_eq⟩ z
    use z * h, z * k
    rw [a_eq]
    rw [mul_add, ← mul_assoc, ← mul_assoc]

  let B := (Int.natAbs '' A) \ {0}
  -- Show B is non-empty by constructing an element
  have hB_nonempty : ∃ b : ℕ, b ∈ B := by
    use (0*x + 1*y).natAbs
    change (0*x + 1*y).natAbs ∈ Int.natAbs '' A \ {0}
    rw [Set.mem_diff_singleton]
    constructor
    · apply Set.mem_image_of_mem Int.natAbs
      use (discharger := rfl) 0, 1
    · rwa [Int.zero_mul, Int.one_mul, Int.zero_add, @Ne.eq_def, Int.natAbs_eq_zero]
  -- By well-ordering principle on subsets of ℕ, B has a minimal element
  -- Call that minimal element "d"
  let Bmin : ℕ := Nat.find hB_nonempty
  have hBmin_spec : (∃ d ∈ A, d.natAbs = Bmin) ∧ Bmin ≠ 0 := Nat.find_spec hB_nonempty
  rcases hBmin_spec.1 with ⟨d, hd⟩
  have hdA := hd.1
  have hdAbs_eq_Bmin:= hd.2
  have hBmin_neq_0 := hBmin_spec.2
  have hdAbs_neq_0 : d.natAbs ≠ 0 := by rwa [← hdAbs_eq_Bmin] at hBmin_neq_0
  have hd_min : ∀ z ∈ A, z.natAbs = 0 ∨ d.natAbs ≤ z.natAbs := by
    intro z hz
    by_cases hzAbs : z.natAbs = 0
    · left
      assumption
    · right
      have hBmin_min := Nat.find_min' hB_nonempty (m := z.natAbs)
        ⟨Set.mem_image_of_mem Int.natAbs hz, hzAbs⟩
      rwa [hdAbs_eq_Bmin]

  have hd_div_A : ∀ a ∈ A, d ∣ a := by
    intro a ha_A
    -- By division algorithm, x = qd + r for some q,r with 0 ≤ r < d
    let q := a / d
    let r := a % d
    have a_eq_quotRem : a = q*d + r := Eq.symm (Int.ediv_add_emod' a d)
    have r_eq : r = (-q)*d + a := by
      rw [← neg_add_eq_iff_eq_add, Int.neg_mul_eq_neg_mul] at a_eq_quotRem
      symm; assumption
    have rAbs_lt_dAbs : r.natAbs < d.natAbs := by
      apply Int.emod_natAbs_lt_of_nonzero
      assumption
    have hr_A : r ∈ A := by
      rw [r_eq]
      apply A_add
      · apply A_mul; assumption
      · assumption
    by_cases hr_eq_0 : r = (0 : ℤ)
    · rw [a_eq_quotRem, hr_eq_0, Int.add_zero]
      exact Int.dvd_mul_left q d
    · rw [← Int.natAbs_eq_zero] at hr_eq_0
      have hd_min_r := hd_min r hr_A
      contrapose hd_min_r
      push_neg
      constructor <;> assumption

  have hxA : x ∈ A := by use 1, 0; simp only [Int.one_mul, Int.zero_mul, Int.add_zero]
  have d_dvd_x : d ∣ x := hd_div_A x hxA

  have hyA : y ∈ A := by use 0, 1; simp only [Int.zero_mul, Int.one_mul, Int.zero_add]
  have d_dvd_y : d ∣ y := hd_div_A y hyA

  obtain ⟨h, k, d_eq⟩ := hdA
  use (discharger := skip) h, k
  rw [isGCD]
  refine' ⟨_, _, _⟩
  · rwa [← d_eq]
  · rwa [← d_eq]
  · rintro c c_dvd_x c_dvd_y
    rw [Int.dvd_def] at c_dvd_x c_dvd_y ⊢
    rcases c_dvd_x with ⟨cx, hcx⟩
    rcases c_dvd_y with ⟨cy, hcy⟩
    use (h * cx + k * cy)
    rw [Int.mul_add, Int.mul_left_comm c h _, Int.mul_left_comm c k _, ← hcx, ← hcy]
    -- this gives errors
    -- exact Dvd.dvd.linear_comb c_dvd_x c_dvd_y h k

#print bezout_identity
-- set_option maxHeartbeats 200000
-- -- set_option trace.AntiUnify true
example : True := by
  autogeneralize ℤ in bezout_identity
  trivial
