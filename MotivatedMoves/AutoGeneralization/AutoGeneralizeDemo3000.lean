/- - - - - - - - - - - - - - - - - - - -
Proof-based generalization
- - - - - - - - - - - - - - - - - - - -/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Finset.Basic

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic3000
import MotivatedMoves.AutoGeneralization.library
open Autogeneralize library

open Real
open Lean Elab Tactic Meta Term Command

-- Uncomment below to hide proofs of "let" statements in the LeanInfoview
set_option pp.showLetValues false
-- set_option pp.explicit true
-- set_option pp.all true
-- set_option profiler true
set_option linter.unusedVariables false

open  PrettyPrinter Delaborator in
@[app_unexpander OfNat.ofNat]
def unexpandOfNat : Unexpander
  | `($(_) $a) => `($a)
  | _ => throw ()



/---------------------------------------------------------------------------
An example where "3" doesn't show up in the proof term, so the proof doesn't generalize.
I.e. compatible proofs must use deduction rules, not computation rules
---------------------------------------------------------------------------/

example := by
  let two_times_three_is_even: Even (2*3) := by
    simp only [Nat.reduceMul]; unfold Even; use 3
  -- autogeneralize (3:ℕ) in two_times_three_is_even -- throws error
  assumption

example := by
  let two_times_three_is_six : 2*3=6 := by simp only [Nat.reduceMul]
  autogeneralize 3 in two_times_three_is_six
  assumption

/- --------------------------------------------------------------------------
An example where "=3" is a required property, so the proof doesn't generalize.
-------------------------------------------------------------------------- -/

theorem six_is_even : Even 6 := by
  unfold Even
  use 3

example := by
  let two_times_three_is_even : Even (2*3) := by
    unfold Even; apply Exists.intro 3; rw [two_mul]

  autogeneralize 3 in two_times_three_is_even


  assumption

example := by
  let two_times_three_is_even : Even (2*3) := by
    simp only [Nat.reduceMul]; apply six_is_even
  -- autogeneralize 3 in two_times_three_is_even -- throws error
  assumption

variable {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α]


example :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}



  autogeneralize 3 in fun_set







  specialize @fun_set.Gen 4
  assumption



example :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}

  autogeneralize 3 in fun_set at occurrences [1]







  specialize @fun_set.Gen 4
  assumption






/- --------------------------------------------------------------------------
DEMO OF HARD CASE -- four 3s in the theorem statement.  2 are related, 2 not.
-------------------------------------------------------------------------- -/

example :
  ∀ {α β : Type} [Fintype α] [Fintype β]  [DecidableEq α], Fintype.card α = 4 → Fintype.card β = 5 → Fintype.card (α → β) = 5 ^ 4 :=
by
  let fun_set : ∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
                  Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α β _ _ _ α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}

  autogeneralize 3 in fun_set

  specialize @fun_set.Gen 4 5

  assumption



/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example:
sqrt(2) is irrational generalizes to sqrt(prime) is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/


example : True := by
  let sum_irrat : Irrational (sqrt (2:ℕ) + 2) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}

  autogeneralize (2:ℕ) in sum_irrat
  simp


example :
  ∀ {α β : Type} [Fintype α] [Fintype β]  [DecidableEq α], Fintype.card α = 4 → Fintype.card β = 5 → Fintype.card (α → β) = 5 ^ 4 :=
by
  let fun_set : ∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
                  Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α β _ _ _ α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}

  autogeneralize 3 in fun_set

  specialize @fun_set.Gen 4 5

  assumption


example : True := by
  let _sum_irrat : Irrational ((sqrt (2:ℕ)) + 2) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}

  autogeneralize (2:ℕ) in _sum_irrat










  specialize _sum_irrat.Gen 3 (Nat.prime_three) 6
  -- specialize _sum_irrat.Gen 3 (Nat.prime_three)
  simp

-- def Irrational' (y : ℝ) :  ∀ y: ℝ, y*y=(2:ℝ)

-- OPTION 1 def square_root (y : ℝ ) :
-- theorem sqrt2irr : ∀ y: ℝ, y*y=(2:ℝ) → Irrational y := sorry
-- theorem sqrt2plus2irr : ∀ y: ℝ, y*y=(2:ℝ) → Irrational (2+y) := sorry

-- OPTION 2 square root of absolute value of 2..

-- option 3 - -2 is still prime

-- option 4 - fix the proof for nats to not involve 1 + 2

example  : True  := by

  let _sqrt2Irrational : ¬ ∃ x : ℚ, x*x = (2:ℕ) := by {apply irrat_def'; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Prime.dvd_mul (Int.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h]; rfl): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; apply Iff.mp (Int.mul_eq_mul_left_iff (Prime.ne_zero (Int.prime_two): (2:ℤ) ≠ 0)) at h; rw [mul_comm 2 k, ← mul_assoc] at h; have b_div : 2 ∣ b := by {have c := (Prime.dvd_mul (Int.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k)):2 ∣ b*b); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd}

  autogeneralize_basic (2:ℕ) in _sqrt2Irrational
  simp at _sqrt2Irrational.Gen
  specialize _sqrt2Irrational.Gen 3 Int.prime_three

  simp



example  : True  := by

  let _sqrt2Irrational : ¬ ∃ x : ℚ, x*x = (2:ℤ) := by {apply irrat_def'; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Prime.dvd_mul (Int.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h]): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; apply Iff.mp (Int.mul_eq_mul_left_iff (Prime.ne_zero (Int.prime_two): (2:ℤ) ≠ 0)) at h; rw [mul_comm 2 k, ← mul_assoc] at h; have b_div : 2 ∣ b := by {have c := (Prime.dvd_mul (Int.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k)):2 ∣ b*b); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Prime.not_dvd_one (Int.prime_two) p_dvd_gcd}

  autogeneralize_basic (2:ℤ ) in _sqrt2Irrational



  have h := True








  simp
/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example:
sqrt(2) is irrational generalizes to sqrt(prime) is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/


example : True := by

  let _sqrt2Irrational : Irrational (sqrt 2) := by apply Nat.prime_two.irrational_sqrt

  autogeneralize_basic 2 in _sqrt2Irrational






  simp















example : Irrational (sqrt 3) := by
  let _sqrt2Irrational : Irrational (sqrt (2: ℕ)) := by apply Nat.prime_two.irrational_sqrt
  autogeneralize_basic (2:ℕ) in _sqrt2Irrational -- adds _sqrt2Irrational.Gen to list of hypotheses

  specialize _sqrt2Irrational.Gen 3 (Nat.prime_three)
  assumption

















/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example of a naive, over-specialized generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+prime is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/


example : True := by

  let _sum_irrat : Irrational ((sqrt (2:ℕ)) + (2:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}

  autogeneralize_basic (2:ℕ) in _sum_irrat






  specialize _sum_irrat.Gen 3 (Nat.prime_three)
  simp






example : Irrational (sqrt 3 + 3) := by
  let _sum_irrat : Irrational (sqrt (2:ℕ) + (2:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}
  autogeneralize_basic (2:ℕ) in _sum_irrat

  specialize _sum_irrat.Gen 3 (Nat.prime_three)
  assumption














/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example of a better, constant-aware generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+nat is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/




example : Irrational (sqrt 3 + 6) := by
  let _sum_irrat : Irrational (sqrt (2:ℕ) + (2:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}
  autogeneralize (2:ℕ) in _sum_irrat

  specialize _sum_irrat.Gen 3 (Nat.prime_three) 6
  -- specialize _sum_irrat.Gen 3 (Nat.prime_three)
  assumption


















/- --------------------------------------------------------------------------
DEMO OF HARD & EASY CASE -- The formula for the distance between any two points in ℝ² -- autogeneralize works fine when there's only one instance of what to generalize
-------------------------------------------------------------------------- -/

example :  ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) :=
by
  let _distance : ∀ (x y : EuclideanSpace (ℝ:Type) (Fin 2)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq.{0,0} x y

  autogeneralize 2 in _distance at occurrences [1 2 3 4]  -- says this formula works for any f-dimensional space as long as distance is given by (∑ i, dist (x i) (y i) ^ f)

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

  autogeneralize_basic Mul.mul in _multComm  -- (.*.) -- adds multPermute.Gen to list of hypotheses

  specialize _multComm.Gen Mul.mul Mul.mul Nat.mul_comm 1 2
  assumption

example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let mult_permute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize_basic Mul.mul in mult_permute

  specialize mult_permute.Gen (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption


example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let mult_permute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize Mul.mul in mult_permute

  specialize mult_permute.Gen (.+.) (.+.) (.+.) (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption

example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let mult_permute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize Mul.mul in mult_permute

  specialize mult_permute.Gen (.+.) (.+.) (.+.) (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption
