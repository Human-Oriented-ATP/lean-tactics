/-
Proof-based generalization
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic3000
import MotivatedMoves.AutoGeneralization.library
open Autogeneralize library

open Real
open Lean Elab Tactic Meta Term Command

-- Uncomment below to hide proofs of "let" statements in the LeanInfoview
set_option pp.showLetValues true
-- set_option pp.explicit true
-- set_option pp.all true
-- set_option profiler true
/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example:
sqrt(2) is irrational generalizes to sqrt(prime) is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

#check dvd_iff_exists_eq_mul_right.mpr
#check Eq.symm
#check Prime.dvd_of_dvd_pow
#check Prime.dvd_mul
#check Int.prime_two

example  : True  := by

  let _sqrt2Irrational : ¬ ∃ x : ℚ, x*x = (2:ℤ) := by {apply irrat_def'; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Prime.dvd_mul (Int.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h]): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; apply Iff.mp (Int.mul_eq_mul_left_iff (Prime.ne_zero (Int.prime_two): (2:ℤ) ≠ 0)) at h; rw [mul_comm 2 k, ← mul_assoc] at h; have b_div : 2 ∣ b := by {have c := (Prime.dvd_mul (Int.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k)):2 ∣ b*b); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd}

  autogeneralize_basic (2:ℤ) in _sqrt2Irrational



  have h := True












  simp
example  : ¬ ∃ x : ℚ, x^2 = (3:ℤ)  := by
  let _sqrt2Irrational : ¬ ∃ x : ℚ, x^2 = (2:ℤ) := by {apply irrat_def; intros h; obtain ⟨a,b, ⟨copr, h ⟩⟩ := h; have a_pow_div : 2 ∣ a^2 := by {apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b^2)}; have a_div : 2 ∣ a := by {apply Prime.dvd_of_dvd_pow (Int.prime_two) a_pow_div}; have a_is_pk : ∃ k, a = 2*k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; clear a_pow_div hk; rw [mul_pow] at h; replace h := Eq.symm h; have p_not_zero: (2:ℤ) ≠ 0 := Prime.ne_zero (Int.prime_two); rw [pow_succ (2:ℤ) 1, mul_assoc] at h; apply Iff.mp (Int.mul_eq_mul_left_iff p_not_zero) at h; rw [pow_one] at h; have b_pow_div : 2 ∣ b^2 := by {apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (k^2)}; have b_div : 2 ∣ b := by {apply Prime.dvd_of_dvd_pow (Int.prime_two) b_pow_div}; clear h k b_pow_div; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd;}
  autogeneralize_basic (2:ℤ) in _sqrt2Irrational -- adds _sqrt2Irrational.Gen to list of hypotheses
  specialize _sqrt2Irrational.Gen (3:ℤ) (Int.prime_three)
  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example:
sqrt(2) is irrational generalizes to sqrt(prime) is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
example : Irrational (Real.sqrt 3) := by
  let _sqrt2Irrational : Irrational (Real.sqrt (2: ℕ)) := by apply Nat.prime_two.irrational_sqrt
  autogeneralize_basic (2:ℕ) in _sqrt2Irrational -- adds _sqrt2Irrational.Gen to list of hypotheses

  specialize _sqrt2Irrational.Gen 3 (Nat.prime_three)
  assumption

















/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example of a naive, over-specialized generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+prime is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
example : Irrational (Real.sqrt 3 + 3) := by
  let _sum_irrat : Irrational (Real.sqrt (2:ℕ) + (2:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}
  autogeneralize_basic (2:ℕ) in _sum_irrat

  specialize _sum_irrat.Gen 3 (Nat.prime_three)
  assumption














/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example of a better, constant-aware generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+nat is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
example : Irrational (Real.sqrt 3 + 6) := by
  let _sum_irrat : Irrational (Real.sqrt (2:ℕ) + (2:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}
  autogeneralize (2:ℕ) in _sum_irrat
  autogeneralize (2:ℕ) in _sum_irrat.Gen

  specialize _sum_irrat.Gen.Gen 6 3 (Nat.prime_three)
  -- specialize _sum_irrat.Gen 3 (Nat.prime_three)
  assumption









/- --------------------------------------------------------------------------
DEMO OF HARD CASE -- four 3s in the theorem statement.  2 are related, 2 not.
-------------------------------------------------------------------------- -/
example :
  ∀ {α β : Type} [Fintype α] [Fintype β]  [DecidableEq α], Fintype.card α = 4 → Fintype.card β = 4 → Fintype.card (α → β) = 4 ^ 4 :=
by
  let _fun_set : ∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
                  Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α β _ _ _ α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}

  autogeneralize_basic 3 in _fun_set
  specialize @_fun_set.Gen 4
  assumption












/- --------------------------------------------------------------------------
DEMO OF HARD CASE -- four 3s in the theorem statement.  2 are related, 2 not.
-------------------------------------------------------------------------- -/
example :
  ∀ {α β : Type} [Fintype α] [Fintype β]  [DecidableEq α], Fintype.card α = 4 → Fintype.card β = 5 → Fintype.card (α → β) = 5 ^ 4 :=
by
  let _fun_set : ∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
                  Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α β _ _ _ α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}

  autogeneralize 3 in _fun_set
  autogeneralize 3 in _fun_set.Gen

  specialize @_fun_set.Gen.Gen 5 4

  assumption










/- --------------------------------------------------------------------------
DEMO OF HARD & EASY CASE -- The formula for the distance between any two points in ℝ² -- autogeneralize works fine when there's only one instance of what to generalize
-------------------------------------------------------------------------- -/

example :  ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) :=
by
  let _distance : ∀ (x y : EuclideanSpace (ℝ:Type) (Fin 2)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq.{0,0} x y

  autogeneralize 2 in _distance  -- says this formula works for any f-dimensional space as long as distance is given by (∑ i, dist (x i) (y i) ^ f)

  intros x y
  specialize _distance.Gen 3 (EuclideanSpace.dist_eq) x y -- x is not a member of a 3-dimensional space such that the distance is given by (∑ i, dist (x i) (y i) ^3)
  assumption

example :  ∀ (x y : EuclideanSpace ℝ (Fin 4)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := by
  let _distance : ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq x y
  autogeneralize 3 in _distance

  intros x y
  specialize _distance.Gen 4 x y
  assumption
/---------------------------------------------------------------------------
Analogizing a theorem about an operator that uses commutativity and associativity
---------------------------------------------------------------------------/
example :  1 * 2 = 2 * 1 := by
  -- let _multComm :  ∀ (n m : ℕ), n * m = m * n := by {intros n m; apply Nat.mul_comm}
  let _multComm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm

  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multComm  -- (.*.) -- adds multPermute.Gen to list of hypotheses

  specialize _multComm.Gen ( fun a b => b * a) (fun _ _ => rfl) 1 2
  assumption

example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let _multPermute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize_basic (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute  -- adds multPermute.Gen to list of hypotheses

  specialize _multPermute.Gen (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption


example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let _multPermute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute  -- adds multPermute.Gen to list of hypotheses
  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute.Gen
  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute.Gen.Gen
  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute.Gen.Gen.Gen
  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute.Gen.Gen.Gen.Gen

  -- specialize all 4 of the instances
  specialize _multPermute.Gen.Gen.Gen.Gen.Gen (.+.) (.+.) (.+.) (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption
