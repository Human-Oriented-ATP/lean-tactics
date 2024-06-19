/-
Proof-dependent generalization,
As described in paper 'Generalization in Type Theory Based Proof Assistants'
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Qq

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic3000

open Real
open Autogeneralize
open Lean Elab Tactic Meta Term Command


-- Uncomment below to hide proofs of "let" statements in the LeanInfoview
set_option pp.showLetValues false
-- set_option profiler true
-- set_option pp.explicit true

-- set_option pp.proofs false
-- set_option pp.proofs.withType true
set_option pp.instanceTypes true

/- --------------------------------------------------------------------------
DEMO OF REALLY HARD CASE -- four 3s in the theorem statement.  2 are related, 2 not.
-------------------------------------------------------------------------- -/
open Qq

-- #eval show MetaM Bool from do
--   let e1 := q(∀ {a : Type} [inst: BEq a], a)
--   let e2 := q(∀ (a : Type) (inst : BEq a), a)
--   isDefEq e1 e2

-- the following expressions aren't unifying! aha it was just synthetic opaqueness
-- #check q(∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
--   Fintype.card α = (2 : ℕ) → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3)

-- #check q(∀ (α β : Type) (inst : Fintype α) (inst_1 : Fintype β) (inst_2 : DecidableEq α),
--   Fintype.card α = ?m.4944 → Fintype.card β = ?m.4943 → Fintype.card (α → β) = ?m.4943 ^ ?m.4944)

-- #eval show MetaM Bool from do
--   let e1 := q(∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
--   Fintype.card α = (2 : ℕ) → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3)

--   let e2 := q(∀ (α β : Type) (inst : Fintype α) (inst_1 : Fintype β) (inst_2 : DecidableEq α),
--   Fintype.card α = 2 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3)

--   isDefEq e1 e2

variable {α β : Type} [Fintype α] [Fintype β]  [DecidableEq α]

set_option trace.Meta.isDefEq true in
example : Fintype.card α = 4 → Fintype.card β = 5 → Fintype.card (α → β) = 5 ^ 4 := by
  let _fun_set : ∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
                  Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := fun {α β} [Fintype α] [Fintype β] [DecidableEq α] fa fb => Eq.mpr (id (congrArg (fun _a => _a = 3 ^ 3) Fintype.card_fun)) (Eq.mpr (id (congrArg (fun _a => Fintype.card β ^ _a = 3 ^ 3) fa)) (Eq.mpr (id (congrArg (fun _a => _a ^ 3 = 3 ^ 3) fb)) (Eq.refl (3 ^ 3))))
  autogeneralize _fun_set (3:ℕ)

  specialize _fun_set.Gen 4 5
  apply _fun_set.Gen


/- --------------------------------------------------------------------------
DEMO OF HARD & EASY CASE -- The formula for the distance between any two points in ℝ² -- autogeneralize works fine when there's only one instance of what to generalize
-------------------------------------------------------------------------- -/

-- #check EuclideanSpace.dist_eq.{0,0} ℝ

-- attribute [reducible] WithLp
example :  ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := by
  let _distance : ∀ (x y : EuclideanSpace (ℝ:Type) (Fin 2)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq.{0,0} x y

  autogeneralize _distance (2:ℕ)  -- says this formula works for any f-dimensional space as long as distance is given by (∑ i, dist (x i) (y i) ^ f)

  intros x y
  specialize _distance.Gen 3 2 (fun _ _ _ _ => EuclideanSpace.dist_eq) x -- x is not a member of a 3-dimensional space such that the distance is given by (∑ i, dist (x i) (y i) ^3)
  sorry

-- attribute [reducible] WithLp
example :  ∀ (x y : EuclideanSpace ℝ (Fin 4)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := by
  let _distance : ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq x y
  autogeneralize _distance (3:ℕ)

  intros x y
  specialize _distance.Gen 4 x y
  assumption
/---------------------------------------------------------------------------
Analogizing a theorem about an operator that uses commutativity and associativity
---------------------------------------------------------------------------/
example :  1 * 2 = 2 * 1 := by
  -- let _multComm :  ∀ (n m : ℕ), n * m = m * n := by {intros n m; apply Nat.mul_comm}
  let _multComm :  ∀ (n m : ℕ), n * m = m * n := Nat.mul_comm

  autogeneralize _multComm (@HMul.hMul ℕ ℕ  ℕ instHMul) -- (.*.) -- adds multPermute.Gen to list of hypotheses

  specialize _multComm.Gen ( fun a b => b * a) (fun _ _ => rfl) 1 2
  assumption


example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let _multPermute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize _multPermute (@HMul.hMul ℕ ℕ  ℕ instHMul) -- (.*.) -- adds multPermute.Gen to list of hypotheses
  specialize _multPermute.Gen (.+.) (.+.) (.+.)
  --                            f:+, then f+ and g++ and assoc, then h+ and comm, ...
  -- specialize _multPermute.Gen (@HAdd.hAdd ℕ ℕ ℕ instHAdd) Nat.add_assoc Nat.add_comm 1 2 3
  assumption

/- --------------------------------------------------------------------------
DEMO OF EASY & HARD CASE -- sqrt(2)+2 is irrational, generalizes to something over-specific -- prime f -> sqrt(f)+f is irrational
-------------------------------------------------------------------------- -/

example : Irrational (Real.sqrt 3) := by
  let _sqrt2Irrational : Irrational (Real.sqrt (2: ℕ)) := by apply Nat.prime_two.irrational_sqrt
  autogeneralize _sqrt2Irrational (2 : ℕ) -- adds _sqrt2Irrational.Gen to list of hypotheses

  specialize _sqrt2Irrational.Gen 3 (Nat.prime_three)
  assumption

example : Irrational (Real.sqrt 3 + 6) := by
  let _sum_irrat : Irrational (Real.sqrt (2:ℕ) + (2:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}
  autogeneralize _sum_irrat (2:ℕ)
  autogeneralize _sum_irrat.Gen (2:ℕ)

  specialize _sum_irrat.Gen.Gen 6 3 (Nat.prime_three)
  -- specialize _sum_irrat.Gen 3 (Nat.prime_three)
  assumption
