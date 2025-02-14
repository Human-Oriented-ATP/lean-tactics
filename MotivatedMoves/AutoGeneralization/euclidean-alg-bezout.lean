import Lean
import Mathlib.Tactic

/-- Bézout's identity states that for any two integers a and b, there exist integers x and y such that their greatest common divisor g can be expressed as a linear combination ax + by = g -/
theorem bezout_identity (x y : ℤ) :
  x ≠ 0 → y ≠ 0 → ∃ (h k : ℤ),  h * x + k * y = (Int.gcd a b) :=
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
    let p : ℕ → Prop := fun n => n ∈ B

    have p_decidable : DecidablePred p := by
      intro n
      apply Classical.propDecidable

    have exists_p : ∃ n, p n := by
      rcases h_B_nonempty with ⟨z, hz⟩
      use z

    let d := Nat.find exists_p
    use d
    constructor
    · exact Nat.find_spec exists_p
    · intro z hz
      exact Nat.find_min' exists_p hz


  -- Call that minimal element "d"
  let ⟨d, hd⟩ := h_B_min
  clear h_B_nonempty
  clear h_B_min

  -- Prove d | x
  have d_dvd_x : (d:ℤ) ∣ x := by
  -- have d_dvd_x : d ∣ x.natAbs := by
    -- Get h,k such that d = hx + ky
    rcases hd.1 with ⟨h, k, hd_eq, d_neq_zero⟩
    -- rw [hd_eq]

    -- Prove d > 0
    have d_pos : 0 < d := by
      rw [hd_eq]
      exact Int.natAbs_pos.mpr d_neq_zero

    have d_neq_zero' : (d:ℤ) ≠ 0 := by exact Int.natCast_ne_zero_iff_pos.mpr d_pos
    have d_pos' : (d:ℤ) > 0 := by exact Int.ofNat_pos.mpr d_pos

    -- By division algorithm, x = qd + r for some q,r with 0 ≤ r < d
    let q := x / d
    let r := x % d
    have x_eq : x = q*d+r  := Eq.symm (Int.ediv_add_emod' x ↑d)
    -- have := Int.emod_nonneg x d_neq_zero'
    have hr_nonneg : 0 ≤ r := by apply Int.emod_nonneg x d_neq_zero'
    have hr_lt : r < d := by apply Int.emod_lt_of_pos x d_pos'

    --  Nat.mod_lt x.natAbs d_pos
    -- let q := x.natAbs / d
    -- let r := x.natAbs % d
    -- have hr_nonneg : 0 ≤ r := Nat.zero_le r
    -- have hr_lt : r < d := Nat.mod_lt x.natAbs d_pos
    -- have x_eq : x.natAbs = q*d+r  := Eq.symm (Nat.div_add_mod' x.natAbs d)

    -- Solve for r
    -- x = q(hx + ky) + r
    -- r = x - q(hx + ky)
    -- r = x(1 - qh) - qky which is in A

    -- If r ≠ 0, then r.natAbs ∈ B and r.natAbs < d, contradicting minimality
    -- by_contra r_nz


    have r_in_A : (r:ℤ) ∈ A := by
      by_cases d_sign : h*x + k*y > 0
      · -- Case hx + ky > 0
        use (1-q*h)
        use (-q*k)

        have r_eq : r = x - q*d := by rw [x_eq]; ring_nf
        rw [r_eq, hd_eq]
        have d_abs_is_d : (h * x + k * y).natAbs = h * x + k * y := by
          rw [Int.natCast_natAbs, abs_eq_self]
          exact Int.le_of_lt d_sign
        rw [d_abs_is_d]
        ring_nf

      · -- Case hx + ky ≤ 0
        sorry
        -- use (- q*h)
        -- use (-q*k)


        -- ring_nf
        -- simp

    have r_abs_in_B : r.natAbs ∈ B := by
      use (1 - q*h)
      use (-q*k)
      constructor
      · rw [Int.ediv_add_emod x d]
        ring_nf
      · exact r_nz

    -- This contradicts minimality of d
    have := hd.2 r.natAbs r_abs_in_B
    have := lt_of_lt_of_le hr_lt this
    exact Nat.lt_irrefl d this

    -- Therefore r = 0 and d|x
    rw [Int.ediv_add_emod x d] at r_nz
    exact ⟨q, by rw [r_nz]; ring⟩

  sorry
