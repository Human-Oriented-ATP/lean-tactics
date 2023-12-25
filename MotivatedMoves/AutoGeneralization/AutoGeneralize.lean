/-
Proof-dependent generalization,
As described in paper 'Generalization in Type Theory Based Proof Assistants'
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.Coprime.Lemmas
open Real

/---------------------------------------------------------------------------
A theorem that sqrt 2 is irrational
---------------------------------------------------------------------------/

theorem sqrt_2_irrational : Irrational (Real.sqrt 2) :=
  sorry

/---------------------------------------------------------------------------
A theorem that sqrt of any prime p is irrational (from mathlib)
---------------------------------------------------------------------------/

theorem sqrt_p_irrational (hp : Nat.Prime p) : Irrational (Real.sqrt p) :=
  @irrational_sqrt_of_multiplicity_odd p (Int.coe_nat_pos.2 hp.pos) p ⟨hp⟩ <| by
    simp [multiplicity.multiplicity_self
      (mt isUnit_iff_dvd_one.1 (mt Int.coe_nat_dvd.1 hp.not_dvd_one))]

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
Using generalize to suppose the operation is not necessarily assoc/comm
---------------------------------------------------------------------------/

def myToExpr : Tactic := fun stx =>
  withMainContext do


theorem multPermute' : ∀ (n m p : Nat), n * (m * p) = m * (n * p) :=
by
  intros n m p
  generalize hf : @HMul.hMul Nat Nat Nat instHMul = f
  -- clear hf -- removing that assumption from context, to fully generalize
  rw [← hf]-- now this is false, so we need to revert it
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

/---------------------------------------------------------------------------
A theorem that uses the coprimality of two numbers
---------------------------------------------------------------------------/
theorem bothPrimeMeansGCDIs1 : ∀ (a b : Nat), a ≠ b → Nat.Prime a → Nat.Prime b → gcd a b = 1 := by
  intros a b aneqb pa pb
  have copr := Nat.coprime_primes pa pb
  apply Iff.mpr at copr
  exact copr aneqb

#print multPermute -- the proof term

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
#print flt_example

theorem flt_example' : 2^4 % 5 = 1 := by
  generalize ha: 2 = a
  generalize hn: 5 = n
  generalize hm: 4 = m
  rw[ ←ha, ←hn, ←hm]
  rfl

#check Nat.Prime.coprime_iff_not_dvd
#check Nat.Coprime.isCoprime

theorem flt_example'' : 2^4 % 5 = 1 % (5 : ℤ):= by
  have hp2 : Nat.Prime 2 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have ne25 : 2 ≠ 5 := by norm_num
  have hcp := Iff.mpr (Nat.coprime_primes hp2 hp5) ne25
  have hcp' := Nat.Coprime.isCoprime hcp
  have flt := Int.ModEq.pow_card_sub_one_eq_one hp5 hcp'
  assumption
#print flt_example''

theorem flt_example''' : 2^4 % 5 = 1 % 5 := by
  have hp2 : Nat.Prime 2 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have ne25 : 2 ≠ 5 := by norm_num
  have hcp := Iff.mpr (Nat.coprime_primes hp2 hp5) ne25
  -- unfold Nat.Coprime at hcp
  -- unfold Nat.gcd at hcp
  assumption
#print flt_example'''

-- The naive first step is to notice all we need is for 2 and 5 to be unequal primes)

theorem flt_general (hneq : a ≠ p) (hp : Nat.Prime p) (ha : Nat.Prime a) : a ^ (p - 1) % p = 1 := by
  have hcp := Iff.mpr (Nat.coprime_primes ha hp) hneq
  have flt := Int.ModEq.pow_card_sub_one_eq_one hp (Nat.Coprime.isCoprime hcp)
  assumption

-- The next step is to notice we need even less -- we just need a and p to be coprime, and p prime.
theorem flt_general' (hp : Nat.Prime p) (hpn : IsCoprime a p) : a ^ (p - 1) % p = 1 := by
  sorry
