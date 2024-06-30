import Lean
import Mathlib.FieldTheory.Finite.Basic

namespace library

theorem irrat_def_aux (n: ℤ) : (∃ x : ℚ, x^2 = (n:ℤ)) → ∃a b : ℤ, gcd a b = 1 ∧ a^2 = (n:ℤ) * b^2:= by
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
  have := irrat_def_aux
  simp at this
  apply this

theorem irrat_def_aux' (n: ℤ) : (∃ x : ℚ, x*x = (n:ℤ)) → ∃a b : ℤ, gcd a b = 1 ∧ a^2 = (n:ℤ) * b^2:= by
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
  rw [Rat.mul_self_num] at hx
  rw [Rat.mul_self_den] at hx
  simp at *
  norm_cast

theorem irrat_def' (n: ℤ) : (¬ ∃a b : ℤ, gcd a b = 1 ∧ a^2 = (n:ℤ) * b^2 )→ ¬(∃ x : ℚ, x*x = (n:ℤ)) := by
  contrapose
  simp
  have := irrat_def_aux'
  simp at this
  apply this

theorem _sqrt2Irrational_xx : ¬ ∃ x : ℚ, x*x = (2:ℤ) := by
  apply irrat_def'
  intros h
  obtain ⟨a, b, ⟨copr, h⟩⟩ := h
  have a_pow_div : 2 ∣ a^2 := by
    apply (Iff.mpr dvd_iff_exists_eq_mul_right)
    use (b^2)
  have a_div : 2 ∣ a := by
    apply Prime.dvd_of_dvd_pow (Int.prime_two) a_pow_div
  have a_is_pk : ∃ k, a = 2 * k := by
    apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div
  obtain ⟨k, hk⟩ := a_is_pk
  rw [hk] at h
  clear a_pow_div hk
  rw [mul_pow] at h
  replace h := Eq.symm h
  have p_not_zero : (2:ℤ) ≠ 0 := Prime.ne_zero (Int.prime_two)
  rw [pow_succ (2:ℤ) 1, mul_assoc] at h
  apply Iff.mp (Int.mul_eq_mul_left_iff p_not_zero) at h
  rw [pow_one] at h
  have b_pow_div : 2 ∣ b^2 := by
    apply (Iff.mpr dvd_iff_exists_eq_mul_right)
    use (k^2)
  have b_div : 2 ∣ b := by
    apply Prime.dvd_of_dvd_pow (Int.prime_two) b_pow_div
  clear h k b_pow_div
  have p_dvd_gcd : 2 ∣ gcd a b := by
    apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩
  clear a_div b_div
  rw [copr] at p_dvd_gcd
  apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd

theorem _sqrt2Irrational_xx_oneline : ¬ ∃ x : ℚ, x*x = (2:ℤ) := by {apply irrat_def'; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_pow_div : 2 ∣ a^2 := by {apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b^2)}; have a_div : 2 ∣ a := by {apply Prime.dvd_of_dvd_pow (Int.prime_two) a_pow_div}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; clear a_pow_div hk; rw [mul_pow] at h; replace h := Eq.symm h; have p_not_zero : (2:ℤ) ≠ 0 := Prime.ne_zero (Int.prime_two); rw [pow_succ (2:ℤ) 1, mul_assoc] at h; apply Iff.mp (Int.mul_eq_mul_left_iff p_not_zero) at h; rw [pow_one] at h; have b_pow_div : 2 ∣ b^2 := by {apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (k^2)}; have b_div : 2 ∣ b := by {apply Prime.dvd_of_dvd_pow (Int.prime_two) b_pow_div}; clear h k b_pow_div; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd}

theorem _sqrt2Irrational_xsq : ¬ ∃ x : ℚ, x^2 = (2:ℤ) := by {apply irrat_def; intros h; obtain ⟨a,b, ⟨copr, h ⟩⟩ := h; have a_pow_div : 2 ∣ a^2 := by {apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b^2)}; have a_div : 2 ∣ a := by {apply Prime.dvd_of_dvd_pow (Int.prime_two) a_pow_div}; have a_is_pk : ∃ k, a = 2*k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; clear a_pow_div hk; rw [mul_pow] at h; replace h := Eq.symm h; have p_not_zero: (2:ℤ) ≠ 0 := Prime.ne_zero (Int.prime_two); rw [pow_succ (2:ℤ) 1, mul_assoc] at h; apply Iff.mp (Int.mul_eq_mul_left_iff p_not_zero) at h; rw [pow_one] at h; have b_pow_div : 2 ∣ b^2 := by {apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (k^2)}; have b_div : 2 ∣ b := by {apply Prime.dvd_of_dvd_pow (Int.prime_two) b_pow_div}; clear h k b_pow_div; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd;}

theorem _sqrt3Irrational_xcu : ¬ ∃ x : ℚ, x^2 = (3:ℤ) := by {apply irrat_def; intros h; obtain ⟨a,b, ⟨copr, h ⟩⟩ := h; have a_pow_div : (3:ℤ) ∣ a^2 := by {apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b^2)}; have a_div : (3:ℤ) ∣ a := by {apply Prime.dvd_of_dvd_pow (Int.prime_three) a_pow_div}; have a_is_pk : ∃ k, a = (3:ℤ)*k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; clear a_pow_div hk; rw [mul_pow] at h; replace h := Eq.symm h; have p_not_zero: (3:ℤ) ≠ 0 := Prime.ne_zero (Int.prime_three); rw [pow_succ (3:ℤ) 1, mul_assoc] at h; apply Iff.mp (Int.mul_eq_mul_left_iff p_not_zero) at h; rw [pow_one] at h; have b_pow_div : (3:ℤ) ∣ b^2 := by {apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (k^2)}; have b_div : (3:ℤ) ∣ b := by {apply Prime.dvd_of_dvd_pow (Int.prime_three) b_pow_div}; clear h k b_pow_div; have p_dvd_gcd : (3:ℤ) ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Prime.not_dvd_one (Int.prime_three) p_dvd_gcd;}

end library
