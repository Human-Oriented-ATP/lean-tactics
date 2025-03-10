import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic
-- import MotivatedMoves.AutoGeneralization.library
import Mathlib.Tactic
open Autogeneralize

example : True := by
  let hyp :  NeZero (1 : ℝ) := NeZero.one
  autogeneralize 1 in hyp
  trivial

section CompRuleInMainType

def even_five_implies_even_fifteen : Even 5 → Even 15 :=
  Even.mul_left (b := 3)

example : True := by
  autogeneralize 5 in even_five_implies_even_fifteen
  /- Output: `∀ (n : ℕ), Even n → Even (3 * n)`
     Desired output: `∀ (n : ℕ), Even n → Even (3 * n)`
     Works correctly! -/
  trivial

def even_six : Even 6 :=
  even_add_self 3

example : True := by
  autogeneralize 6 in even_six
  /- Output: `Even (3 + 3)`
     Desired output: `?`
    (maybe it would have to be `∀ n : Nat, Even n → Even n`
     if we want the output to necessarily have a free variable in place of `6`.) -/
  trivial

def two_equals_two : 2 = 2 := rfl

example : True := by
  autogeneralize 2 in two_equals_two
  /- Output: `∀ n : ℕ, n = n`
     Desired output: `∀ n : ℕ, n = n`
     Works correctly! -/
  trivial

end CompRuleInMainType


section CompRuleInAppArg

theorem three_is_odd : Odd 3 :=
  Nat.Prime.odd_of_ne_two (p := 3) Nat.prime_three (by decide)

#print three_is_odd
#check decide

example : True := by
  autogeneralize 3 in three_is_odd
  /- Output: `error`
     Desired output: `∀ {p : ℕ} (hp : Nat.Prime p) (h_two : p ≠ 2), Odd p`

     ERROR:
     Inferred type: `true = true`
     Expected type: `decide (?n ≠ 2) = true`
      -/
  trivial

#check of_decide_eq_true -- this function may have to be handled separately in the algorithm

lemma three_not_equals_two : 3 ≠ 2 := by decide

theorem three_is_odd' : Odd 3 :=
  Nat.Prime.odd_of_ne_two (p := 3) Nat.prime_three three_not_equals_two

example : True := by
  autogeneralize 3 in three_is_odd'
  /- Output: `∀ (n : ℕ), Nat.Prime n → n ≠ 2 → Odd n`
     Desired output: `∀ {p : ℕ} (hp : Nat.Prime p) (h_two : p ≠ 2), Odd p`
     Works correctly! -/
  trivial


end CompRuleInAppArg


section CompRuleInAppFn

end CompRuleInAppFn


section CompRuleInFnDomain

end CompRuleInFnDomain


section CompRuleInFnBody

end CompRuleInFnBody
