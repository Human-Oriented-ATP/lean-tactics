import Lean
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Irrational
open Real

namespace library

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
PRODUCT OF NON-MULTIPLES OF K
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

abbrev ndiv [Dvd α] (a b : α) : Prop := ¬(a ∣ b)
infix:50 " ∤ " => ndiv
-- notation a "∤" b => ¬(a ∣ b)

lemma ndvd_to_mod {n : ℕ} : 2 ∤ n ↔ n % 2 = 1 := Nat.two_dvd_ne_zero

lemma mod_means_exists_k (m n r : ℕ) (r_lt_n : r < n): m % n = r ↔ ∃ k, n * k + r = m := by
  constructor
  {
    intro h
    use m / n
    simp only [Nat.mod_def] at h
    rw [← h]
    refine Nat.add_sub_of_le ?h.h
    exact Nat.mul_div_le m n
  }
  {
    rintro ⟨k, hk⟩
    rw [← hk]
    rw [Nat.mul_comm]
    refine Nat.mul_add_mod_of_lt ?mpr.intro.h
    exact r_lt_n
  }

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
IRRATIONALITY OF SQUARE ROOTS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

theorem irrat_def (n: ℕ) : (¬ ∃a b : ℕ, gcd a b = 1 ∧ a*a = (n: ℕ) * b*b ) → Irrational (Real.sqrt n) := by
  contrapose
  simp
  intros irr
  unfold Irrational at irr
  simp at irr
  obtain ⟨x, irr⟩ := irr
  have x_pos : 0 ≤ (x:ℝ) := by
    have sqrt_pos := Real.sqrt_nonneg (n: ℝ)
    rw [← irr] at sqrt_pos
    apply sqrt_pos
  have n_pos : 0 ≤ (n:ℝ) := by
    exact Nat.cast_nonneg n
  -- rw [← Real.sqrt_mul_self x_pos] at irr
  have x_sq : x*x=n := by
    symm
    apply_mod_cast (Real.sqrt_eq_iff_mul_self_eq n_pos x_pos).mp (irr.symm)
  norm_num at x_pos
  have x_num_pos := (@Rat.num_nonneg x).mpr x_pos
  clear x_pos
  use Int.natAbs x.num
  use x.den
  constructor
  apply x.reduced
  -- rw [← Rat.num_div_den x] at x_sq
  rw [Rat.eq_iff_mul_eq_mul] at x_sq
  simp at x_sq

  rw [Rat.mul_self_num] at x_sq
  rw [Rat.mul_self_den] at x_sq

  have num_abs_eq_num : x.num = Int.natAbs x.num := Int.eq_natAbs_of_zero_le x_num_pos
  rw [num_abs_eq_num] at x_sq; clear num_abs_eq_num x_num_pos
  rw [mul_assoc n x.den x.den]
  apply_mod_cast x_sq


end library
