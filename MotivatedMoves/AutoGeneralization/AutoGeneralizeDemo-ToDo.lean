import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.Coprime.Lemmas

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic

open Real
open Autogeneralize

-- Uncomment below to hide proofs of "let" statements in the LeanInfoview
set_option pp.showLetValues false

/---------------------------------------------------------------------------
A theorem that uses FLT -- a version that requires coprimality
---------------------------------------------------------------------------/

theorem flt_example : 2^4 % (3 : ℤ) = (1 : ℤ) % (3 : ℤ):= by
  have hp2 : Nat.Prime 2 := by exact Nat.prime_two
  have hp5 : Nat.Prime 3 := by exact Nat.prime_three
  have ne25 : 2 ≠ 3 := by norm_num
  have hcp := Iff.mpr (Nat.coprime_primes hp2 hp5) ne25
  have hcp' := Nat.Coprime.isCoprime hcp
  have flt := Int.ModEq.pow_card_sub_one_eq_one hp5 hcp'
  assumption


example: True := by
  let h := flt_example
  autogeneralize h 3

/---------------------------------------------------------------------------
A theorem that uses FLT -- a version that only requires primality
---------------------------------------------------------------------------/

theorem flt_example' : (6: ℤ) ^3 % 3 = 6 % 3 := by
  have := ZMod.pow_card (6 : ZMod 3)
  sorry


example: True := by
  let h := flt_example'
  autogeneralize h 3


/---------------------------------------------------------------------------
Generalizing the theorem about GCDs from integers to polynomials
---------------------------------------------------------------------------/
example : True := by
  let _gcdlincomb : ∀ a b : ℤ, ∃ x y : ℤ, gcd a b = a*x + b*y := by {intros a b; exact exists_gcd_eq_mul_add_mul a b}
  autogeneralize _gcdlincomb ℤ  -- adds _gcdlincomb.Gen to list of hypotheses
  -- autogeneralize _gcdlincomb.Gen LinearOrderedCommRing
  -- specialize _gcdlincomb.Gen (Polynomial ℤ) (inferInstance) inferInstance
  -- inferInstance (Polynomial.normalizedGcdMonoid ℝ)
  simp

/---------------------------------------------------------------------------
Trying to get gcd problem to work if you don't put the proof in directly into the hypothesis
---------------------------------------------------------------------------/

theorem gcdof2and3 : gcd 2 3 = 1 := by
  have neq2and3 : 2 ≠ 3 := by simp
  have p2 : Nat.Prime 2 := Nat.prime_two
  have p3 : Nat.Prime 3 := Nat.prime_three
  have copr := Nat.coprime_primes p2 p3
  apply Iff.mpr at copr
  apply Nat.Coprime.gcd_eq_one
  exact copr (neq2and3)

theorem gcdof2and3' : gcd 2 3 = 1 := Nat.Coprime.gcd_eq_one $ Iff.mpr (Nat.coprime_primes Nat.prime_two Nat.prime_three) (by simp)


example : True := by
  let _gcdof2and3 :  gcd 2 3 = 1 :=  gcdof2and3

  autogeneralize _gcdof2and3 (3: ℕ)

  simp

example : True := by
  let _gcdof2and3 :  gcd 2 3 = 1 :=  gcdof2and3'

  autogeneralize _gcdof2and3 (3: ℕ)

  simp

/---------------------------------------------------------------------------
A theorem that uses the coprimality of two numbers
TO DO: should work for any prime not equal to 3.
  right now, it generalizes to any prime

  issue: the proof that 2 ≠ 3 doesn't actualy involve 3.  it says "Not ((Nat.succ.injEq 1 2))..."
---------------------------------------------------------------------------/

example : gcd 3 3 = 1 := by
  let _gcdof2and3 : gcd 2 3 = 1 := Nat.Coprime.gcd_eq_one $ Iff.mpr (Nat.coprime_primes Nat.prime_two Nat.prime_three) (by simp)

  autogeneralize _gcdof2and3 (3: ℕ)

  specialize _gcdof2and3.Gen 3 (Nat.prime_three)
  assumption

-- will generalize saying you need the generalized-3 to be prime
-- but really, you just need the generalized-3 to be coprime to 5
