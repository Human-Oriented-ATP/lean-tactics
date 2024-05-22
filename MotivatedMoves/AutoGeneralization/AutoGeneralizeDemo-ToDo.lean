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

/---------------------------------------------------------------------------
Analogizing the theorem that any prime has GCD 1 with 3 (to the theorem that any prime has GCD 1 with 2)
---------------------------------------------------------------------------/
example : Nat.gcd 19 2 = 1 := by
  let _coprimality : ∀ p : ℕ, p ≠ 3 → Nat.Prime p → Nat.gcd p 3 = 1:= fun p neq pp => Nat.Coprime.gcd_eq_one ((Nat.coprime_primes pp Nat.prime_three).mpr neq)
  autogeneralize _coprimality 3 -- adds _coprimality.Gen to list of hypotheses

  specialize _coprimality.Gen 2 Nat.prime_two 19 (by simp) (by exact (Nat.prime_iff_card_units 19).mpr rfl)
  assumption

  -- you should be able to tell that the proof doesn't need Prime f and Prime p
  -- it only needs Coprime f p

/---------------------------------------------------------------------------
In any subset of of n even and 1 odd number (all ≤ 2n), two are coprime.
---------------------------------------------------------------------------/
theorem gcd_consec_eq_one (x : ℕ) : Nat.Coprime x (x+1) := by
  simp only [Nat.coprime_self_add_right, Nat.coprime_one_right_eq_true]

theorem exists_coprime_pair : ∀ n : ℕ, n > 2
→ ∀ S ⊆ Finset.range (2*n+1),
(S.filter (Even .)).card = n → (S.filter (Odd .)).card = 1
→ ∃ a ∈ S, ∃ b ∈ S, Nat.Coprime a b := by
  intros n nge2 S S_range card_even card_odd

  have exists_odd : ∃ o ∈ S, ¬Even o := by {
    have card_odd_pos : (Finset.filter (fun x => Odd x) S).card > 0 := by linarith
    have nonempty_odd : (Finset.filter (fun x => Odd x) S).Nonempty := ((Finset.filter (fun x => Odd x) S).card_pos).mp card_odd_pos
    have := nonempty_odd.to_subtype
    simp at this
    assumption
  }
  clear card_odd

  let ⟨o, ⟨o_in_s, o_odd ⟩⟩ := exists_odd
  clear exists_odd

  use o; simp [o_in_s]
  use (o+1); simp [gcd_consec_eq_one]

  have o_plus_one_even : Even (o+1) := by exact Nat.even_add_one.mpr o_odd
  have o_plus_one_leq_2n: o+1 ≤ 2*n := by {
    have o_leq: o ≤ 2*n := by exact Finset.mem_range_succ_iff.mp (S_range o_in_s)
    have o_neq: o ≠ 2*n := by {intro o_even; apply o_odd; use n; linarith }
    have o_le : o < 2*n := Nat.lt_of_le_of_ne o_leq o_neq
    exact o_le
  }

  have S_has_all_evens : ∀ x : ℕ, Even x → x ≤ 2*n → x ∈ S := by {
    simp at *
    -- simp [card_even, S_range]
    intros x x_even x_leq_2n
    by_contra x_notin_S
    sorry
    -- --since x_notin_S, and it is disjoint with S,
    -- -- then by card_even, there are at least 11 even elements in S.
    -- -- But there can't be 11 even numbers in a finset.range of size 2n.
    -- -- contradiction.
    -- have total_evens_in_range_is_n : Finset.card (Finset.filter Even (Finset.range (2*n+1))) = n := by {
    --   simp only [Finset.card_filter, Finset.card_range,Nat.add_one, Nat.two_mul]
    -- -- We need to prove that in a set of 2n consecutive natural numbers, exactly n are even.
    -- -- We will use the sum function over the range from 0 to 2n (exclusive) and count the even numbers.

    -- -- This completes the proof.
    -- }
    -- have x_in_S : x ∈ S := by {
    --   have all_evens_in_S : Finset.filter Even S = Finset.filter Even (Finset.range (2*n+1)) := by {
    --     apply Finset.filter_subset_filter
    --     exact S_range
    --   }
    --   rw [←all_evens_in_S, total_evens_in_range_is_n] at x_notin_S
    -- }

  }

  apply S_has_all_evens (o+1) o_plus_one_even o_plus_one_leq_2n
