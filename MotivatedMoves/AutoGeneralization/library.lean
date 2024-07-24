import Lean
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Irrational
open Real

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



theorem irrat_def_aux' (n: ℤ) : (∃ x : ℚ, x*x = (n:ℤ)) → ∃a b : ℤ, gcd a b = 1 ∧ a*a = (n:ℤ) * b*b:= by
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

  rw [Rat.mul_self_num] at hx
  rw [Rat.mul_self_den] at hx
  simp at *
  rw [mul_assoc]
  norm_cast

theorem irrat_def_aux'' (n: ℤ) : (∃ x : ℚ, x*x = (n:ℤ)) → ∃a b : ℤ, gcd a b = 1 ∧ a^2 = (n:ℤ) * b^2:= by
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

theorem irrat_def_aux2' (n: ℤ) (n_pos : n ≥ 0) : ¬(∃ x : ℚ, x*x = (n:ℤ)) → Irrational (sqrt (n:ℤ)) := by
  contrapose
  intro h
  unfold Irrational at h
  simp at h
  simp

  obtain ⟨x,h⟩ := h
  use x

  have c := (@sqrt_eq_cases n x).mp (Eq.symm h)
  cases c with
  | inl h =>
      obtain ⟨c1,c2⟩ := h
      norm_cast at c1
  | inr h =>
      obtain ⟨c1,c2⟩ := h
      simp at c1
      linarith
  --     by_contra c
  --     norm_cast at c2
  --     norm_cast at c1
  --     rw [c2] at h
  --     rw [c2] at c
  --     simp at c
  --     simp




  -- intros h
  -- unfold Irrational
  -- simp
  -- simp at h
  -- intros x
  -- specialize h x

  -- intro a
  -- have c := (@sqrt_eq_cases n x).mp (Eq.symm a)

  -- cases c with
  -- | inl h =>
  --     obtain ⟨c1,c2⟩ := h
  --     norm_cast at c1
  -- | inr h =>
  --     obtain ⟨c1,c2⟩ := h
  --     norm_cast at c2
  --     norm_cast at c1
  --     rw [c2] at h
  --     rw [c2] at a
  --     simp at h
  --     simp at a
  --     replace a := (@sqrt_eq_zero' n).mp (Eq.symm a)





  -- by_cases n_pos : n ≥ 0
  -- have sq := sqrt_mul_self_eq_abs n
  -- simp a


theorem irrat_def'' (n: ℤ) : (¬ ∃a b : ℤ, gcd a b = 1 ∧ a^2 = (n:ℤ) * b^2 )→ ¬(∃ x : ℚ, x*x = (n:ℤ)) := by
  contrapose
  simp
  have := irrat_def_aux''
  simp at this
  apply this

theorem irrat_def' (n: ℤ) : (¬ ∃a b : ℤ, gcd a b = 1 ∧ a*a = (n:ℤ) * b*b )→ ¬(∃ x : ℚ, x*x = (n:ℤ)) := by
  contrapose
  simp
  have := irrat_def_aux'
  simp at this
  apply this

  -- theorem irrat_def'_nat (n: ℕ) : (¬ ∃a b : ℕ, gcd a b = 1 ∧ a*a = (n:ℕ) * b*b )→ ¬(∃ x : ℚ, x*x = (n:ℕ)) := by
  -- contrapose
  -- simp
  -- have := irrat_def_aux'
  -- simp at this
  -- apply this

-- theorem def_irrat (n: ℤ) (n_pos : n ≥ 0): (¬ ∃a b : ℤ, gcd a b = 1 ∧ a^2 = (n:ℤ) * b^2 )→ Irrational (sqrt (n:ℤ)) := by
--   contrapose
--   simp
--   have a := irrat_def_aux' n
--   have b := irrat_def_aux2' n n_pos

--   simp at this
--   apply this




-- theorem _sqrt2Irrational_copr : ¬∃ a b, gcd a b = 1 ∧ a ^ 2 = 2 * b ^ 2 := by
--   intros h
--   obtain ⟨a, b, ⟨copr, h⟩⟩ := h
--   have a_pow_div : 2 ∣ a^2 := by
--     apply (Iff.mpr dvd_iff_exists_eq_mul_right)
--     use (b^2)
--   have a_div : 2 ∣ a := by
--     apply Prime.dvd_of_dvd_pow (Int.prime_two) a_pow_div
--   have a_is_pk : ∃ k, a = 2 * k := by
--     apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div
--   obtain ⟨k, hk⟩ := a_is_pk
--   rw [hk] at h
--   clear a_pow_div hk
--   rw [mul_pow] at h
--   replace h := Eq.symm h
--   have p_not_zero : (2:ℤ) ≠ 0 := Prime.ne_zero (Int.prime_two)
--   rw [pow_succ (2:ℤ) 1, mul_assoc] at h
--   apply Iff.mp (Int.mul_eq_mul_left_iff p_not_zero) at h
--   rw [pow_one] at h
--   have b_pow_div : 2 ∣ b^2 := by
--     apply (Iff.mpr dvd_iff_exists_eq_mul_right)
--     use (k^2)
--   have b_div : 2 ∣ b := by
--     apply Prime.dvd_of_dvd_pow (Int.prime_two) b_pow_div
--   clear h k b_pow_div
--   have p_dvd_gcd : 2 ∣ gcd a b := by
--     apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩
--   clear a_div b_div
--   rw [copr] at p_dvd_gcd
--   apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd

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
  rw [← Real.sqrt_mul_self x_pos] at irr
  have x_sq : sqrt (x * x) = sqrt n → x*x = n := by apply?
  specialize x_sq irr; clear irr
  norm_num at x_pos
  have x_num_pos := (@Rat.num_nonneg_iff_zero_le x).mpr x_pos
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

  sorry
  -- rw [← Real.sqrt_mul_self] at irr]
  -- apply this

theorem _sqrt2Irrational_xx_aa : ¬ ∃ x : ℚ, x*x = (2:ℤ) := by
  apply irrat_def'
  intros h
  obtain ⟨a, b, ⟨copr, h⟩⟩ := h
  have a_div : 2 ∣ a := by
    have c := (Prime.dvd_mul (Int.prime_two)).mp ((by
    apply (Iff.mpr dvd_iff_exists_eq_mul_right)
    use (b*b)
    rw [← mul_assoc]
    rw [h]): 2 ∣ a*a)
    cases c; assumption; assumption
  have a_is_pk : ∃ k, a = 2 * k := by
    apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div
  obtain ⟨k, hk⟩ := a_is_pk
  rw [hk] at h
  replace h := Eq.symm h
  rw [mul_assoc] at h
  rw [mul_assoc] at h
  apply Iff.mp (Int.mul_eq_mul_left_iff (Prime.ne_zero (Int.prime_two): (2:ℤ) ≠ 0)) at h
  rw [mul_comm 2 k, ← mul_assoc] at h
  have b_div : 2 ∣ b := by
    have c := (Prime.dvd_mul (Int.prime_two)).mp ((by
    apply (Iff.mpr dvd_iff_exists_eq_mul_left)
    use (k*k)):2 ∣ b*b)
    cases c; assumption; assumption
  have p_dvd_gcd : 2 ∣ gcd a b := by
    apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩
  clear a_div b_div
  rw [copr] at p_dvd_gcd
  apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd

theorem _sqrt2Irrational_xx_aa_full : ¬ ∃ x : ℚ, x*x = (2:ℤ) := by
  apply irrat_def'
  intros h
  obtain ⟨a, b, ⟨copr, h⟩⟩ := h
  have a_div : 2 ∣ a := by
    have c := (Prime.dvd_mul (Int.prime_two)).mp ((by
    apply (Iff.mpr dvd_iff_exists_eq_mul_right)
    use (b*b)
    rw [← mul_assoc]
    rw [h]): 2 ∣ a*a)
    cases c; assumption; assumption
  have a_is_pk : ∃ k, a = 2 * k := by
    apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div
  obtain ⟨k, hk⟩ := a_is_pk
  rw [hk] at h
  replace h := Eq.symm h
  rw [mul_assoc] at h
  rw [mul_assoc] at h
  apply Iff.mp (Int.mul_eq_mul_left_iff (Prime.ne_zero (Int.prime_two): (2:ℤ) ≠ 0)) at h
  rw [mul_comm 2 k, ← mul_assoc] at h
  have b_div : 2 ∣ b := by
    have c := (Prime.dvd_mul (Int.prime_two)).mp ((by
    apply (Iff.mpr dvd_iff_exists_eq_mul_left)
    use (k*k)):2 ∣ b*b)
    cases c; assumption; assumption
  have p_dvd_gcd : 2 ∣ gcd a b := by
    apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩
  clear a_div b_div
  rw [copr] at p_dvd_gcd
  apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd

theorem _sqrt2Irrational_xx_aa_full_nat_natprime : Irrational (sqrt 2) := by
  apply irrat_def
  intros h
  obtain ⟨a, b, ⟨copr, h⟩⟩ := h
  have a_div : 2 ∣ a := by
    have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by
    apply (Iff.mpr dvd_iff_exists_eq_mul_right)
    use (b*b)
    rw [← mul_assoc]
    rw [h];
    ): 2 ∣ a*a)
    cases c; assumption; assumption
  have a_is_pk : ∃ k, a = 2 * k := by
    apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div
  obtain ⟨k, hk⟩ := a_is_pk
  rw [hk] at h
  replace h := Eq.symm h
  rw [mul_assoc] at h
  rw [mul_assoc] at h
  rw [mul_comm 2 k] at h
  rw [mul_eq_mul_left_iff] at h
  rw [← mul_assoc k k 2] at h
  have := Nat.Prime.ne_zero Nat.prime_two
  cases h with
  | inl =>
      have b_div : 2 ∣ b := by
        have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by
        apply (Iff.mpr dvd_iff_exists_eq_mul_left)
        use (k*k)))
        cases c; assumption; assumption
      have p_dvd_gcd : 2 ∣ gcd a b := by
        apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩
      clear a_div b_div
      rw [copr] at p_dvd_gcd
      apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd
    | inr => apply this; assumption
  -- simp only [mul_eq_mul_left_iff, Nat.Prime.ne_zero, or_false] at h✝

  -- rw [mul_comm 2 k, ← mul_assoc] at h
  -- have b_div : 2 ∣ b := by
  --   have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by
  --   apply (Iff.mpr dvd_iff_exists_eq_mul_left)
  --   use (k*k)))
  --   cases c; assumption; assumption
  -- have p_dvd_gcd : 2 ∣ gcd a b := by
  --   apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩
  -- clear a_div b_div
  -- rw [copr] at p_dvd_gcd
  -- apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd


theorem _sqrt2Irrational_nat : ¬ ∃ x : ℚ, x*x = (2:ℕ) := by
  apply irrat_def'
  intros h
  obtain ⟨a, b, ⟨copr, h⟩⟩ := h
  have a_div : 2 ∣ a := by
    have c := (Prime.dvd_mul (Int.prime_two)).mp ((by
    apply (Iff.mpr dvd_iff_exists_eq_mul_right)
    use (b*b)
    rw [← mul_assoc]
    rw [h];
    rfl
    ): 2 ∣ a*a)
    cases c; assumption; assumption
  have a_is_pk : ∃ k, a = 2 * k := by
    apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div
  obtain ⟨k, hk⟩ := a_is_pk
  rw [hk] at h
  replace h := Eq.symm h
  rw [mul_assoc] at h
  rw [mul_assoc] at h
  apply Iff.mp (Int.mul_eq_mul_left_iff (Prime.ne_zero (Int.prime_two): (2:ℤ) ≠ 0)) at h
  rw [mul_comm 2 k, ← mul_assoc] at h
  have b_div : 2 ∣ b := by
    have c := (Prime.dvd_mul (Int.prime_two)).mp ((by
    apply (Iff.mpr dvd_iff_exists_eq_mul_left)
    use (k*k)):2 ∣ b*b)
    cases c; assumption; assumption
  have p_dvd_gcd : 2 ∣ gcd a b := by
    apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩
  clear a_div b_div
  rw [copr] at p_dvd_gcd
  apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd


  theorem _sqrt2Irrational_nat_plustwo : Irrational (sqrt 2 + 2) := by
    apply Irrational.add_nat
    apply irrat_def
    intros h
    obtain ⟨a, b, ⟨copr, h⟩⟩ := h
    have a_div : 2 ∣ a := by
      have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by
      apply (Iff.mpr dvd_iff_exists_eq_mul_right)
      use (b*b)
      rw [← mul_assoc]
      rw [h];
      ): 2 ∣ a*a)
      cases c; assumption; assumption
    have a_is_pk : ∃ k, a = 2 * k := by
      apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div
    obtain ⟨k, hk⟩ := a_is_pk
    rw [hk] at h
    replace h := Eq.symm h
    rw [mul_assoc] at h
    rw [mul_assoc] at h
    rw [mul_comm 2 k] at h
    rw [mul_eq_mul_left_iff] at h
    rw [← mul_assoc k k 2] at h
    have := Nat.Prime.ne_zero Nat.prime_two
    cases h with
    | inl =>
        have b_div : 2 ∣ b := by
          have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by
          apply (Iff.mpr dvd_iff_exists_eq_mul_left)
          use (k*k)))
          cases c; assumption; assumption
        have p_dvd_gcd : 2 ∣ gcd a b := by
          apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩
        clear a_div b_div
        rw [copr] at p_dvd_gcd
        apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd
      | inr => apply this; assumption

theorem _sqrt2Irrational_nat_plustwo_oneline : Irrational (sqrt 2 + 2) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}

end library
