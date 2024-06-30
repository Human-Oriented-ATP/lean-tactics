import Lean
import Mathlib.FieldTheory.Finite.Basic

namespace library

theorem irrat_def' (n: ℤ) : (∃ x : ℚ, x^2 = (n:ℤ)) → ∃a b : ℤ, gcd a b = 1 ∧ a^2 = (n:ℤ) * b^2:= by
  intro h
  obtain ⟨x,hx⟩ := h -- (∃ x : ℚ, x^2 = (3:ℤ))

  use x.num
  use x.den
  constructor

  have coprim := x.reduced
  unfold Nat.Coprime at coprim
  rw [← Int.natAbs_cast x.den] at coprim
  rw [← Int.gcd_eq_natAbs] at coprim
  unfold Int.gcd at coprim
  rw [← gcd_eq_nat_gcd] at coprim
  have copr_int : gcd (Int.natAbs x.num) (Int.natAbs x.den) = (1 : ℤ) := by
    rw [coprim]
    rfl
  have copr_int' : gcd (x.num) x.den = (1 : ℤ) := by
    rw [← copr_int]
    rfl
  rw [copr_int']

  norm_cast at hx
  apply Rat.eq_iff_mul_eq_mul.mp at hx

  rw [pow_two]
  rw [pow_two]
  rw [pow_two] at hx
  rw [Rat.mul_self_num] at hx
  rw [Rat.mul_self_den] at hx
  simp at *
  norm_cast

theorem irrat_def (n: ℤ) : (¬ ∃a b : ℤ, gcd a b = 1 ∧ a^2 = (n:ℤ) * b^2 )→ ¬(∃ x : ℚ, x^2 = (n:ℤ)) := by
  contrapose
  simp
  have := irrat_def'
  simp at this
  apply this

end library
