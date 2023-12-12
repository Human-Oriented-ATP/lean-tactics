/-
Proof-dependent generalization,
As described in paper 'Generalization in Type Theory Based Proof Assistants'
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Irrational
open Real

/---------------------------------------------------------------------------
A theorem about irrationality of sqrt 2
---------------------------------------------------------------------------/

theorem sqrt_two_irrational : Irrational (sqrt 2):=
  by sorry

theorem sqrt_prime_irrational {p : ℕ} (hp : Nat.Prime p): Irrational (sqrt p):=
  by sorry

/---------------------------------------------------------------------------
A theorem that uses FLT
---------------------------------------------------------------------------/

-- theorem flt_example : 2^4 ZMOD 5 = 1:= by

theorem flt_example : 2^4 % 5 = 1 := by rfl

theorem flt_example' : 2^4 % 5 = 1 := by
  generalize ha: 2 = a
  generalize hn: 5 = n
  generalize hm: 4 = m
  rw[ ←ha, ←hn, ←hm]
  rfl

theorem flt_example'' : 2^4 % (5 : ℤ) = (1 : ℤ) % (5 : ℤ):= by
  -- generalize ha: 2 = a
  -- generalize hp: 5 = p
  -- rw [Int.ModEq 5 2^4 1]
  have hp : Nat.Prime 5 := sorry
  have hcp : IsCoprime (2: ℤ)  (5: ℤ) := sorry
  have flt := Int.ModEq.pow_card_sub_one_eq_one hp hcp
  rw [Int.ModEq] at flt
  rw [← flt]


#print flt_example


/---------------------------------------------------------------------------
A theorem that uses associativity and commutativity of multiplication
---------------------------------------------------------------------------/
theorem multPermute : ∀ (n m p : Nat), n * (m * p) = m * (n * p) := by
  intros n m p
  rw [← Nat.mul_assoc]
  rw [@Nat.mul_comm n m]
  rw [Nat.mul_assoc]
#print multPermute -- the proof term

/---------------------------------------------------------------------------
Using the generalize tactic, to create a false theorem (you need assoc and comm)
---------------------------------------------------------------------------/
theorem multPermute' : ∀ (n m p : Nat), n * (m * p) = m * (n * p) :=
by
  intros n m p
  generalize hm : @HMul.hMul Nat Nat Nat instHMul = f
  rw [← hm]-- now this is false, so we need to revert it
  apply multPermute

/---------------------------------------------------------------------------
A generalization of the theorem to any binary operation that is assoc & comm
---------------------------------------------------------------------------/
theorem fPermute :
∀ (f : Nat → Nat → Nat)
-- (f_assoc : ∀ (n m p : Nat),  f n (f m p) = f (f n m) p ) -- n (m p) = (n m) p
(f_assoc : ∀ (n m p : Nat),  f (f n m) p = f n (f m p)) -- n (m p) = (n m) p
(f_comm : ∀ (n m : Nat), f n m = f m n)
(n m p : Nat), f n (f m p) = f m (f n p) -- n (m p) = m (n p)
:= by
  intros f f_assoc f_comm n m p
  -- generalize f = fgen
  rw [← f_assoc]
  rw [f_comm n m]
  rw [f_assoc]

/---------------------------------------------------------------------------
Checking that we can instantiate the generalization with addition
---------------------------------------------------------------------------/
theorem addPermute : ∀ (n m p : Nat), n + (m + p) = m + (n + p) := by
  apply fPermute _ Nat.add_assoc Nat.add_comm
