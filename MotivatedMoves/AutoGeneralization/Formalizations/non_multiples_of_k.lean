import Lean
import Mathlib.Data.Real.Irrational

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
