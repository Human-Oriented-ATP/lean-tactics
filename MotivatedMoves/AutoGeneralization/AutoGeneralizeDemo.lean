/-
Proof-dependent generalization,
As described in paper 'Generalization in Type Theory Based Proof Assistants'
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic

open Real
open Autogeneralize

-- Uncomment below to hide proofs of "let" statements in the LeanInfoview
set_option pp.showLetValues false
-- set_option pp.explicit true

-- set_option pp.proofs false
-- set_option pp.proofs.withType true
-- set_option pp.instanceTypes true

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


/---------------------------------------------------------------------------
The formula for the distance between any two points in ℝ²
---------------------------------------------------------------------------/

-- USE THIS LIBRARY https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html#EuclideanSpace

-- OR DEFINE IT MYSELF -- define euclidean distance myself like below
-- def euclidean_distance {n : ℕ} (x y : fin n → ℝ) : ℝ :=
--   (∑ i : fin n, (x i - y i) * (x i - y i))^(1/2)

-- theorem 2d_euclidean_distance : ∀ (x y : ℝ × ℝ),
--   Euclidean.dist x y  = ((x.1 - y.1)^2 + (x.2 - y.2)^2)^(1/2) := by
--   simp [Euclidean.dist]
--   sorry

theorem distance : ∀ (x y : EuclideanSpace ℝ (Fin 2)),
  dist x y = sqrt (dist (x 0) (y 0) ^ 2 + dist (x 1) (y 1) ^ 2) :=
by
  intros x y
  have d := EuclideanSpace.dist_eq x y
  simp at d
  assumption

-- theorem distance : ∀ (x y : EuclideanSpace ℝ (fin 2)),
--   Euclidean.dist x y  = ((x 0 - y 0)^2 + (x 1 - y 1)^2)^(1/2) := by
--   simp [Euclidean.dist]
--   sorry

-- theorem distance : ∀ (x y : ℝ × ℝ),
--   Euclidean.dist x y  = ((x.1 - y.1)^2 + (x.2 - y.2)^2)^(1/2) := by
--   simp [Euclidean.dist]
--   sorry

-- theorem distance : ∀ (x y : fin 2 → ℝ),
--   Euclidean.dist x y  = ((x 0 - y 0)^2 + (x 1 - y 1)^2)^(1/2) := by
--   simp [Euclidean.dist]
--   sorry
