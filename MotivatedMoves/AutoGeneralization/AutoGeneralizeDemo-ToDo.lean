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
Given integers a and b, you can write their gcd as a linear combination of a and b
---------------------------------------------------------------------------/
theorem gcd_as_lin_comb : ∀ a b : ℤ, ∃ x y : ℤ, gcd a b = a*x + b*y := by
  intros a b
  exact exists_gcd_eq_mul_add_mul a b

/---------------------------------------------------------------------------
Generalizing the theorem about GCDs from integers to polynomials
---------------------------------------------------------------------------/
example : True := by
  simp
