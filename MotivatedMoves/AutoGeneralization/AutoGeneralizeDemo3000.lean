/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Proof-based generalization.
Accounts for constants playing the same role in different places.
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic3000
import MotivatedMoves.AutoGeneralization.library
open Autogeneralize library

open Real
open Lean Elab Tactic Meta Term Command

set_option linter.unusedVariables false
set_option pp.showLetValues false
-- set_option pp.explicit true
-- set_option profiler true


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING PROOFS OF IRRATIONALITY.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--
Example:
sqrt(2) is irrational generalizes to sqrt(prime) is irrational
-/
example : Irrational (sqrt 3) := by
  let sum_irrat : Irrational (sqrt (2:ℕ)) := by {apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize_basic (2:ℕ) in sum_irrat
  specialize sum_irrat.Gen 3 (Nat.prime_three)
  assumption

/--
Example of a naive, over-specialized generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+prime is irrational
-/
example : Irrational (sqrt 3 + 3) := by
  let sum_irrat : Irrational (sqrt (2:ℕ) + 2) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize_basic (2:ℕ) in sum_irrat
  specialize sum_irrat.Gen 3 (Nat.prime_three)
  assumption

/--
Example of a better, constant-aware generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+nat is irrational
-/
example : Irrational (sqrt 3 + 6) := by
  let sum_irrat : Irrational (sqrt (2:ℕ) + 2) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize (2:ℕ) in sum_irrat
  specialize sum_irrat.Gen 3 (Nat.prime_three) 6
  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING SIZES OF SETS.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

variable {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α]

/--
Example of a naive, over-specialized generalization:
This generalizes all four 3s in the same way. (There are four 3s in the theorem statement.  2 are related, 2 not.)
-/
example : Fintype.card α = 4 → Fintype.card β = 4 → Fintype.card (α → β) = 4 ^ 4 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize_basic 3 in fun_set
  specialize @fun_set.Gen 4
  assumption

/--
Example of a better, constant-aware generalization:
Generalizes the pairs of 3s separately.
-/
example : Fintype.card α = 4 → Fintype.card β = 5 → Fintype.card (α → β) = 5 ^ 4 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize 3 in fun_set
  specialize @fun_set.Gen 4 5
  assumption

/--
Demonstration of functionality to generalize at specified occurrences.
This generalizes just the first pair of 3s.
-/
example : Fintype.card α = 4 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 4 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize 3 in fun_set at occurrences [1]
  specialize @fun_set.Gen 4
  assumption

/--
Demonstration of functionality to generalize at specified occurrences.
This generalizes just the second pair of 3s.
-/
example : Fintype.card α = 3 → Fintype.card β = 4 → Fintype.card (α → β) = 4 ^ 3 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize 3 in fun_set at occurrences [2]
  specialize @fun_set.Gen 4
  assumption


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING FUNCTIONS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--
Generalizing an operator that only requires commutativity.
-/

example :  1 + 2 = 2 + 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm
  autogeneralize_basic Mul.mul in mult_comm -- generalize all
  specialize mult_comm.Gen Add.add Nat.add_comm 1 2
  assumption

example :  1 + 2 = 2 + 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm
  autogeneralize Mul.mul in mult_comm -- generalize all, separately
  specialize mult_comm.Gen Add.add Add.add Nat.add_comm 1 2
  assumption

example :  1 * 2 = 2 * 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm
  autogeneralize (HMul.hMul) in mult_comm at occurrences [1] -- generalize at first occurrence
  specialize mult_comm.Gen Mul.mul Nat.mul_comm 1 2
  assumption

example :  1 + 2 = (2 + 1)*1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = (m * n) * 1 :=  by {intros a b; rw [Nat.mul_one]; apply Nat.mul_comm}
  autogeneralize (HMul.hMul) in mult_comm at occurrences [1 3] -- generalize just at first and third occurrences, separately
  specialize mult_comm.Gen Add.add Add.add (Nat.mul_one) Nat.add_comm 1 2
  assumption

/--
Generalizing an operator that requires commutativity and associativity.
Generalizes all instances of * in the same way.
-/
example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let mult_permute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize_basic Mul.mul in mult_permute
  specialize mult_permute.Gen (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption

/--
Generalizing an operator that requires commutativity and associativity.
Generalizes all instances of * separately.
-/
example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let mult_permute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize Mul.mul in mult_permute
  specialize mult_permute.Gen (.+.) (.+.) (.+.) (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING WITH COMPUTATION RULES
Demonstration that compatible proofs must use deduction rules, not computation rules
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--
An example where only deduction rules are used, so the proof generalizes.
-/
example := by
  let two_times_three_is_even : Even (2*3) := by {unfold Even; apply Exists.intro 3; rw [two_mul]}
  autogeneralize 3 in two_times_three_is_even
  assumption

/--
An example where "3" doesn't show up in the proof term (due to use of the computation rule reduceMul), so the proof doesn't generalize.
-/
theorem six_is_even : Even 6 := by {unfold Even; use 3}
example := by
  let two_times_three_is_even : Even (2*3) := by
    simp only [Nat.reduceMul]; apply six_is_even
  -- autogeneralize 3 in two_times_three_is_even -- throws error b/c of computation rule
  assumption
