import Lean
import Mathlib.Tactic

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic
open Autogeneralize Classical

set_option trace.TypecheckingErrors true
set_option trace.ProofPrinting true

def is_gcd (g a b : ℤ) : Prop := g ∣ a ∧ g ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g)
notation g " is GCD[" a ", " b "]" => is_gcd g a b

theorem bezout_mini' :
    ∀ x y : ℤ,
    y ≠ 0 →
    ∃ h k : ℤ, h * x + k * y ≠ 0
    :=

by
  intros x y y_neq_0
  use 0
  use 1
  rw [zero_mul, one_mul, zero_add]
  exact y_neq_0


example : True := by
  autogeneralize ℤ in bezout_mini'
  trivial




/-- Bézout's identity states that for any two integers a and b, there exist integers x and y such that their greatest common divisor g can be expressed as a linear combination ax + by = g -/
theorem bezout_identity (x y : ℤ) :
  -- x ≠ 0 → y ≠ 0 → ∃ (h k : ℤ),  (hcf a b) = h * x + k * y  :=
    x ≠ 0 → y ≠ 0 → ∃ (h k : ℤ), (h * x + k * y) is GCD[x, y] :=

by
  intros x_neq_0 y_neq_0

  -- Consider the set A = {hx + ky | x,y ∈ ℤ}
  let A := {z : ℤ | ∃ h k : ℤ, z = h * x + k * y}
  -- Consider the set B = {|z| | z ∈ A, z ≠ 0} of non-zero absolute values
  let B := {z : ℕ   | ∃ h k : ℤ, z = (h * x + k * y).natAbs ∧ h * x + k * y ≠ 0}
  -- let B := {z : ℕ | ∃ h k : ℤ, z = |h * x + k * y| ∧ h * x + k * y ≠ 0}

  -- Show B is non-empty by constructing an element
  have h_B_nonempty : B.Nonempty := by
    use (0*x + 1*y).natAbs
    use 0
    use 1
    constructor
    rfl
    simp only [zero_mul, one_mul, zero_add, ne_eq, y_neq_0, not_false_eq_true]

  -- By well-ordering principle on subsets of ℕ, B has a minimal element
  have h_B_min : ∃ d : ℕ, d ∈ B ∧ ∀ z ∈ B, d ≤ z := by

    use Nat.find h_B_nonempty
    constructor
    · exact Nat.find_spec h_B_nonempty
    · intro z hz
      exact Nat.find_min' h_B_nonempty hz


  -- Call that minimal element "d"
  let ⟨d, hd⟩ := h_B_min
  clear h_B_nonempty
  clear h_B_min

  -- Get h,k such that d = hx + ky
  have ⟨h, k, d_eq, d_neq_zero⟩ := hd.1
  use h
  use k

  -- Prove d > 0
  have d_pos : 0 < d := by
    rw [d_eq]
    exact Int.natAbs_pos.mpr d_neq_zero
  have d_neq_zero' : (d:ℤ) ≠ 0 := by exact Int.natCast_ne_zero_iff_pos.mpr d_pos
  have d_pos' : (d:ℤ) > 0 := by exact Int.ofNat_pos.mpr d_pos



  -- -- Prove c | x and c | y => c | d
  -- have d_minimal : ∀ c, c ∣ x → c ∣ y → c ∣ d := by
  --   intro c ⟨kc,c_div_x⟩ ⟨ky,c_div_y⟩
  --   rw [d_eq, c_div_x, c_div_y]
  --   simp only [Int.natCast_natAbs, dvd_abs]

  --   refine (Int.dvd_add_left ?H).mpr ?_
  --   rw [mul_comm, mul_assoc]
  --   exact Int.dvd_mul_right c (ky * k)
  --   rw [mul_comm, mul_assoc]
  --   exact Int.dvd_mul_right c (kc * h)

  -- Prove d | x
  have d_dvd_x : (d:ℤ) ∣ x := by

    -- By division algorithm, x = qd + r for some q,r with 0 ≤ r < d
    let q := x / d
    let r := x % d
    have x_eq : x = q*d+r  := Eq.symm (Int.ediv_add_emod' x ↑d)
    -- have := Int.emod_nonneg x d_neq_zero'
    have r_nonneg : 0 ≤ r := by apply Int.emod_nonneg x d_neq_zero'
    have r_lt_d : r < d := by apply Int.emod_lt_of_pos x d_pos'

    -- If r ≠ 0, then r.natAbs ∈ B and r.natAbs < d, contradicting minimality
    by_cases r_zero : r = 0
    -- If r = 0, then d|x
    rw [r_zero] at x_eq
    use q; rw [x_eq]; simp only [add_zero, mul_comm]

    -- If r ≠ 0, then r.natAbs ∈ B and r.natAbs < d, contradicting minimality of d
    have r_in_A : (r:ℤ) ∈ A := by
      have r_eq : r = x - q*d := by rw [x_eq]; ring_nf

      -- Solve for r
      -- x = q(hx + ky) + r
      -- r = x - q(hx + ky)
      -- r = x(1 - qh) - qky which is in A

      by_cases d_sign : h*x + k*y > 0
      · -- Case hx + ky > 0
        use (1-q*h)
        use (-q*k)

        rw [r_eq, d_eq]

        have d_abs_is_d : (h * x + k * y).natAbs = h * x + k * y := by
          rw [Int.natCast_natAbs, abs_eq_self]
          exact Int.le_of_lt d_sign
        rw [d_abs_is_d]
        ring_nf

      · -- Case hx + ky ≤ 0
        use (1+q*h)
        use (q*k)

        rw [r_eq, d_eq]

        have d_abs_is_neg_d : (h * x + k * y).natAbs = -(h * x + k * y) := by
          rw [Int.natCast_natAbs, abs_eq_neg_self]
          exact Int.not_lt.mp d_sign
        rw [d_abs_is_neg_d]
        ring_nf

    have r_abs_in_B : r.natAbs ∈ B := by
      have ⟨hr,kr, r_eq_hk⟩  := r_in_A
      use hr
      use kr
      constructor
      rw [r_eq_hk]
      rw [← r_eq_hk]; exact r_zero

    -- This contradicts minimality of d
    have d_le_r := hd.2 r.natAbs r_abs_in_B
    clear r_abs_in_B r_in_A r_zero x_eq
    by_contra ctra

    have r_natabs_eq : r.natAbs = r := by
      rw [Int.natCast_natAbs, abs_eq_self]; exact r_nonneg
    rw [← r_natabs_eq] at r_lt_d
    norm_cast at r_lt_d
    have r_lt_r := lt_of_lt_of_le r_lt_d d_le_r
    exact (lt_self_iff_false r.natAbs).mp r_lt_r

  -- Prove d | y
  have d_dvd_y : (d:ℤ) ∣ y := by

    -- By division algorithm, y = qd + r for some q,r with 0 ≤ r < d
    let q := y / d
    let r := y % d
    have y_eq : y = q*d+r  := Eq.symm (Int.ediv_add_emod' y ↑d)
    -- have := Int.emod_nonneg x d_neq_zero'
    have r_nonneg : 0 ≤ r := by apply Int.emod_nonneg y d_neq_zero'
    have r_lt_d : r < d := by apply Int.emod_lt_of_pos y d_pos'

    -- If r ≠ 0, then r.natAbs ∈ B and r.natAbs < d, contradicting minimality
    by_cases r_zero : r = 0
    -- If r = 0, then d|x
    rw [r_zero] at y_eq
    use q; rw [y_eq]; simp only [add_zero, mul_comm]

    -- If r ≠ 0, then r.natAbs ∈ B and r.natAbs < d, contradicting minimality of d
    have r_in_A : (r:ℤ) ∈ A := by
      have r_eq : r = y - q*d := by rw [y_eq]; ring_nf

      -- Solve for r
      -- y = q(hx + ky) + r
      -- r = y - q(hx + ky)
      -- r = y - qhx - qky
      -- r = y(1 - qk) - qhx which is in A

      by_cases d_sign : h*x + k*y > 0
      · -- Case hx + ky > 0
        use (- q*h)
        use (1-q*k)

        rw [r_eq, d_eq]

        have d_abs_is_d : (h * x + k * y).natAbs = h * x + k * y := by
          rw [Int.natCast_natAbs, abs_eq_self]
          exact Int.le_of_lt d_sign
        rw [d_abs_is_d]
        ring_nf

      · -- Case hx + ky ≤ 0
        use (q*h)
        use (1+q*k)

        rw [r_eq, d_eq]

        have d_abs_is_neg_d : (h * x + k * y).natAbs = -(h * x + k * y) := by
          rw [Int.natCast_natAbs, abs_eq_neg_self]
          exact Int.not_lt.mp d_sign
        rw [d_abs_is_neg_d]
        ring_nf

    have r_abs_in_B : r.natAbs ∈ B := by
      have ⟨hr,kr, r_eq_hk⟩  := r_in_A
      use hr
      use kr
      constructor
      rw [r_eq_hk]
      rw [← r_eq_hk]; exact r_zero

    -- This contradicts minimality of d
    have d_le_r := hd.2 r.natAbs r_abs_in_B
    clear r_abs_in_B r_in_A r_zero y_eq
    by_contra ctra

    have r_natabs_eq : r.natAbs = r := by
      rw [Int.natCast_natAbs, abs_eq_self]; exact r_nonneg
    rw [← r_natabs_eq] at r_lt_d
    norm_cast at r_lt_d
    have r_lt_r := lt_of_lt_of_le r_lt_d d_le_r
    exact (lt_self_iff_false r.natAbs).mp r_lt_r

  rw [is_gcd]
  refine' ⟨ _, _, _⟩
  · rw [d_eq] at d_dvd_x
    exact Int.natAbs_dvd.mp d_dvd_x
  · rw [d_eq] at d_dvd_y
    exact Int.natAbs_dvd.mp d_dvd_y
  · intro c c_dvd_x c_dvd_y
    -- specialize d_minimal c c_dvd_x c_dvd_y
    -- rw [d_eq] at d_minimal
    exact Dvd.dvd.linear_comb c_dvd_x c_dvd_y h k

-- set_option maxHeartbeats 200000
-- set_option trace.AntiUnify true
example : True := by
  autogeneralize ℤ in bezout_identity
  trivial
