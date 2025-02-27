import Lean
import Mathlib.Data.Real.Irrational
open Real

namespace library

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GCD Algorithm
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

def Int.mod_decreasing {a b : ℤ}: a ≠ 0 → |b % a| < |a| := by
  intro a_neq_0
  rw [abs_of_nonneg (a := b % a)]
  rw [← Int.emod_abs]
  refine Int.emod_lt_of_pos b ?w₂.H
  rwa [@abs_pos]
  exact Int.emod_nonneg b a_neq_0

def Int.mod_dvd {a b k : ℤ}: k ∣ b % a → k ∣ a → k ∣ b := by
  intros h1 h2
  rw [← Int.ediv_add_emod b a]
  refine Int.dvd_add ?_ h1
  exact Dvd.dvd.mul_right h2 (b / a)

def Int.dvd_mod {a b c : ℤ} : c ∣ a → c ∣ b → c ∣ (b % a) := by
  intro c_div_a c_div_b
  rw [← Int.ediv_add_emod b a] at c_div_b
  have c_div_aq: c ∣ a*(b/a) := Dvd.dvd.mul_right c_div_a (b/a)

  exact (Int.dvd_iff_dvd_of_dvd_add c_div_b).mp c_div_aq

/-- The greatest common divisor of two integers. -/
def Int.hcf (a b : ℤ) : {g : ℤ // g ∣ a ∧ g ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g)} :=
  if h:a = (0 : ℤ) then
    ⟨b, ⟨by simp_all only [dvd_zero], by simp only [dvd_refl], by simp⟩⟩
  else
    let ⟨val, ⟨ha, hb, hdiv⟩⟩ := Int.hcf (b % a) a
    ⟨val, ⟨hb, Int.mod_dvd ‹_› ‹_›, fun c hca hcr ↦ hdiv c (Int.dvd_mod ‹_› ‹_›) hca⟩⟩
  termination_by (abs a).natAbs
  decreasing_by (
    have := Int.mod_decreasing h (b:=b)
    refine Int.natAbs_lt_natAbs_of_nonneg_of_lt ?w₁ this
    exact abs_nonneg (b % a)
  )

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
PRODUCT OF NON-MULTIPLES OF K
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

abbrev ndiv [Dvd α] (a b : α) : Prop := ¬(a ∣ b)
infix:50 " ∤ " => ndiv
-- notation a "∤" b => ¬(a ∣ b)

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

lemma ctrps {p q : Prop} :  (p → q) → (¬ q → ¬ p) := by
  intro a a_1
  simp_all only [imp_false, not_false_eq_true]
lemma mtr {p q : Prop} : (¬ q → ¬ p) → (p → q) := fun h hp ↦ by_contra (fun h' ↦ h h' hp)

lemma mod_means_exists_k' (m n r : ℕ) (r_lt_n : r < n):  m % n ≠ r ↔ ¬ ∃ k, n * k + r = m := by
  have fwd := ctrps (mod_means_exists_k m n r r_lt_n).mp
  have bck := ctrps (mod_means_exists_k m n r r_lt_n).mpr

  constructor
  {
    apply bck
  }
  {
    apply fwd
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
