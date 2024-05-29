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
set_option pp.showLetValues false
-- set_option pp.explicit true

-- set_option pp.proofs false
-- set_option pp.proofs.withType true
-- set_option pp.instanceTypes true


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

  autogeneralize _distance (2:) -- says this formula works for any f-dimensional space as long as distance is given by (∑ i, dist (x i) (y i) ^ f)

  intros x y
  specialize _distance.Gen 3 x -- x is not a member of a 3-dimensional space such that the distance is given by (∑ i, dist (x i) (y i) ^3)
  sorry
