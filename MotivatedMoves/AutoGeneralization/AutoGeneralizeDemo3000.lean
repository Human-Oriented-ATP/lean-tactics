/-
Proof-dependent generalization,
As described in paper 'Generalization in Type Theory Based Proof Assistants'
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic3000

open Real
open Autogeneralize
open Lean Elab Tactic Meta Term Command


-- Uncomment below to hide proofs of "let" statements in the LeanInfoview
set_option pp.showLetValues true
-- set_option pp.explicit true

-- set_option pp.proofs false
-- set_option pp.proofs.withType true
-- set_option pp.instanceTypes true

/---------------------------------------------------------------------------
Analogizing a theorem about an operator that uses commutativity and associativity
---------------------------------------------------------------------------/
example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let _multPermute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize _multPermute (.*.) -- adds multPermute.Gen to list of hypotheses

  specialize _multPermute.Gen (@HAdd.hAdd ℕ ℕ ℕ instHAdd) Nat.add_assoc Nat.add_comm
  specialize _multPermute.Gen 1 2 3
  assumption

/---------------------------------------------------------------------------
Analogizing the theorem that sqrt(2) is irrational (to the theorem that sqrt(3) is irrational)
---------------------------------------------------------------------------/
example : Irrational (Real.sqrt 3) := by
  let _sqrt2Irrational : Irrational (Real.sqrt (2: ℕ)) := by apply Nat.prime_two.irrational_sqrt
  autogeneralize _sqrt2Irrational (2 : ℕ) -- adds _sqrt2Irrational.Gen to list of hypotheses

  specialize _sqrt2Irrational.Gen 3 (Nat.prime_three)
  assumption



/---------------------------------------------------------------------------
DEMO OF SUCCESS -- The formula for the distance between any two points in ℝ² -- autogeneralize works fine when there's only one instance of what to generalize
---------------------------------------------------------------------------/

example :  ∀ (x y : EuclideanSpace ℝ (Fin 4)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := by
  let _distance : ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq x y
  autogeneralize _distance (3:)

  intros x y
  specialize _distance.Gen 4 x y
  assumption

/---------------------------------------------------------------------------
DEMO OF FAILURE -- The formula for the distance between any two points in ℝ² -- now there's two instances of what to generalize...and it overgeneralizes.
---------------------------------------------------------------------------/

example :  ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := by
  let _distance : ∀ (x y : EuclideanSpace ℝ (Fin 2)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq x y

  autogeneralize _distance (2:)  -- says this formula works for any f-dimensional space as long as distance is given by (∑ i, dist (x i) (y i) ^ f)

  intros x y
  specialize _distance.Gen 3 x -- x is not a member of a 3-dimensional space such that the distance is given by (∑ i, dist (x i) (y i) ^3)
  sorry

/---------------------------------------------------------------------------
FAILED EXPERIMENT -- sqrt(2)+3 is irrational.  the "instNatAtLeast2" is confused with the 2 we want to generalize.
---------------------------------------------------------------------------/
example : Irrational (Real.sqrt 2+5) := by
  let _sum_irrat : Irrational (Real.sqrt (2:ℕ) + (4:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}
  autogeneralize _sum_irrat (2:ℕ)
  -- simp at _sum_irrat.Gen
  -- specialize _sum_irrat
  sorry

#print Irrational.add_nat
#print Nat.prime_two
example : True := by
  let _sum_irrat : Irrational (Real.sqrt (2:ℕ) + (2:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}
  -- autogeneralize _sum_irrat 2
  replacePatternWithHoles _sum_irrat (2:ℕ)
  simp

example : True := by
  let _sqrt2Irrational : Irrational (Real.sqrt (2: ℕ)) := by apply Nat.prime_two.irrational_sqrt
  replacePatternWithHoles _sqrt2Irrational (2:)
  simp


/- --------------------------------------------------------------------------
EXPERIMENTATION
---------------------------------------------------------------------------/
example : Irrational (Real.sqrt 2 + 2) := by
  apply Irrational.add_int
  apply Nat.prime_two.irrational_sqrt


#eval (toExpr 2).occurs (toExpr 2)

example : True := by
  let _hyp : Fin 2 → Fin 2 → ℕ := fun (x y : Fin 2) => 2
  -- let _hyp : Fin 2 → ℕ := fun (x : Fin 2) => 2
  replacePatternWithHoles _hyp 2
  sorry

example : True := by
  let _hyp : Fin 2 → Fin 2 → ℕ := fun (x y : Fin 2) => 2
  -- let _hyp : Fin 2 → ℕ := fun (x : Fin 2) => 2
  replacePatternWithHoles _hyp 2
  sorry

example :  ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := by
  let _distance : ∀ (x y : EuclideanSpace ℝ (Fin 2)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq x y
  replacePatternWithHoles _distance (2:)

  sorry
