/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Demos of proof generalization tactic in Lean
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/
import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic

import MotivatedMoves.AutoGeneralization.Formalizations.irrationality_of_sqrts

open Autogeneralize

open Real
open Lean Elab Tactic Meta Term Command

set_option linter.unusedVariables false
set_option pp.showLetValues false
-- set_option trace.ProofPrinting true

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Generalization of the proof that √17 is irrational
to the proof that the square root of any prime is irrational.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example : ∀ (p : ℕ), Nat.Prime p → Irrational √p := by

  /- Start with the theorem that √17 is irrational. -/
  let irrat_sqrt : Irrational (√17) := by {apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 17 ∣ a := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 17 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 17 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 17 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 17] at h; have := Nat.Prime.ne_zero prime_seventeen; cases h with | inl => have b_div : 17 ∣ b := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 17 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (prime_seventeen) p_dvd_gcd | inr => apply this; assumption}

  /- Find the proof-based generalization of 17 to any prime, and add it as a theorem in the context. -/
  autogeneralize (17:ℕ) in irrat_sqrt

  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Generalization of the proof that √17+17 is irrational
to the proof that √p+n is irrational for any prime p and nat n.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example: ∀ (p n : ℕ), Nat.Prime p → Irrational (√p + n) := by
  intros p n p_prime

  /- Start with the theorem that √17 is irrational. -/
  let irrat_sqrt : Irrational (sqrt (17:ℕ)+17) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 17 ∣ a := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 17 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 17 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 17 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 17] at h; have := Nat.Prime.ne_zero prime_seventeen; cases h with | inl => have b_div : 17 ∣ b := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 17 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (prime_seventeen) p_dvd_gcd | inr => apply this; assumption}

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (17:ℕ) in irrat_sqrt

  exact irrat_sqrt.Gen p p_prime n

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Generalization of the proof that |A ∪ B| ≤ 4 when |A|=2 and |B|=2
to the proof that |A ∪ B| ≤ n+m when |A|=n and |B|=m
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example : ∀ (n m : ℕ) (α : Type) [inst : Fintype α] [inst_2 : DecidableEq α] (A B : Finset α),
  A.card = n → B.card = m → (A ∪ B).card ≤ n+m:= by

  /- Start with the theorem that |A ∪ B| ≤ 4 when |A|=2 and |B|=2. -/
  let union_of_finsets (α : Type) [inst : Fintype α] [inst_2 : DecidableEq α] (A B : Finset α) (hA : A.card = 2) (hB : B.card = 2) : (A ∪ B).card ≤ 4 := by apply hA ▸ hB ▸ Finset.card_union_add_card_inter A B ▸ Nat.le_add_right _ _

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (2:ℕ) in union_of_finsets

  assumption
