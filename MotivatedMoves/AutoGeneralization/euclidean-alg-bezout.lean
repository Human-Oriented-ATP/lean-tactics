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
