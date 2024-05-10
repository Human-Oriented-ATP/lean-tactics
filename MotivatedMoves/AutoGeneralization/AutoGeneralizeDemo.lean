/-
Proof-dependent generalization,
As described in paper 'Generalization in Type Theory Based Proof Assistants'
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.Coprime.Lemmas

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic

open Real
open Autogeneralize

-- Uncomment below to hide proofs of "let" statements in the LeanInfoview
set_option pp.showLetValues false
-- set_option pp.proofs true
-- set_option pp.proofs.withType true
-- set_option pp.explicit true
-- set_option pp.instanceTypes true
-- set_option pp.explicit true

/---------------------------------------------------------------------------
Generalizing a theorem about an operator that uses commutativity and associativity
---------------------------------------------------------------------------/
example :  True := by
  let _multPermute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}

  autogeneralize _multPermute (.*.) -- adds multPermute.Gen to list of hypotheses

  simp

/---------------------------------------------------------------------------
Generalizing the theorem that sqrt(2) is irrational
(Note this isn't the most general version of the theorem -- it's a proof-based generalization)
---------------------------------------------------------------------------/
example : True := by
  let _sqrt2Irrational : Irrational (sqrt 2) := by apply Nat.prime_two.irrational_sqrt

  autogeneralize _sqrt2Irrational 2 -- adds _sqrt2Irrational.Gen to list of hypotheses

  simp

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
Analogizing the theorem that integers commute (to the theorem that reals commute)
---------------------------------------------------------------------------/
example : (0.5 : ℝ) + 0.7 = 0.7 + 0.5 := by
  let _comm_nums : ∀ (a b : ℤ), a + b = b + a := by {apply add_comm}
  autogeneralize _comm_nums ℤ

  specialize _comm_nums.Gen ℝ inferInstance
  specialize _comm_nums.Gen 0.5 0.7
  assumption

/---------------------------------------------------------------------------
Analogizing the theorem that any prime has GCD 1 with 3 (to the theorem that any prime has GCD 1 with 2)
---------------------------------------------------------------------------/
example : True := by
  let _coprimality : ∀ p : ℕ, p ≠ 3 → Nat.Prime p → gcd p 3 = 1:= by {intros p neq pp; exact (Iff.mpr $ Nat.coprime_primes pp (Nat.prime_three)) neq}
  autogeneralize _coprimality 3 -- adds _coprimality.Gen to list of hypotheses

  specialize _coprimality.Gen 2 Nat.prime_two
  simp
  -- you should be able to tell that the proof doesn't need Prime f and Prime p
  -- it only needs Coprime f p

/---------------------------------------------------------------------------
Analogizing the theorem about GCDs of integers (to GCDs of polynomials)
---------------------------------------------------------------------------/
example : True := by
  let _gcdlincomb : ∀ a b : ℤ, ∃ x y : ℤ, gcd a b = a*x + b*y := by {intros a b; exact exists_gcd_eq_mul_add_mul a b}
  autogeneralize _gcdlincomb ℤ  -- adds _gcdlincomb.Gen to list of hypotheses
  -- autogeneralize _gcdlincomb.Gen LinearOrderedCommRing
  -- specialize _gcdlincomb.Gen (Polynomial ℤ) (inferInstance) inferInstance
  -- inferInstance (Polynomial.normalizedGcdMonoid ℝ)
  simp

/---------------------------------------------------------------------------
A theorem that uses the coprimality of two numbers
---------------------------------------------------------------------------/
-- theorem bothPrimeMeansGCDIs1 : ∀ (a b : Nat), a ≠ b → Nat.Prime a → Nat.Prime b → gcd a b = 1 := by
--   intros a b aneqb pa pb
--   have copr := Nat.coprime_primes pa pb
--   apply Iff.mpr at copr
--   exact copr aneqb

theorem gcdof2and3 : gcd 2 3 = 1 := by
  have neq2and3 : 2 ≠ 3 := by simp
  have p2 : Nat.Prime 2 := Nat.prime_two
  have p3 : Nat.Prime 3 := Nat.prime_three
  have copr := Nat.coprime_primes p2 p3
  apply Iff.mpr at copr
  exact copr (neq2and3)

example : True := by
  let h := gcdof2and3
  autogeneralize h (3: ℕ)

-- will generalize saying you need the generalized-3 to be prime
-- but really, you just need the generalized-3 to be coprime to 5
