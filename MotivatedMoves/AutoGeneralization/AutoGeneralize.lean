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

theorem sqrt_2_irrational : Irrational (Real.sqrt 2) := Nat.prime_two.irrational_sqrt

/---------------------------------------------------------------------------
A theorem that sqrt of any prime p is irrational (from mathlib)
---------------------------------------------------------------------------/

theorem sqrt_p_irrational (hp : Nat.Prime p) : Irrational (Real.sqrt p) :=
  @irrational_sqrt_of_multiplicity_odd p (Int.coe_nat_pos.2 hp.pos) p ⟨hp⟩ <| by
    simp [multiplicity.multiplicity_self
      (mt isUnit_iff_dvd_one.1 (mt Int.coe_nat_dvd.1 hp.not_dvd_one))]

/---------------------------------------------------------------------------
A theorem about irrationality of sqrt 2
---------------------------------------------------------------------------/

theorem sqrt_two_irrational : Irrational (sqrt 2):=
  by sorry

theorem sqrt_prime_irrational {p : ℕ} (hp : Nat.Prime p): Irrational (sqrt p):=
  by sorry

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
theorem multPermute' : ∀ (n m p : Nat), n * (m * p) = m * (n * p) :=
by
  intros n m p
  generalize hm : @HMul.hMul Nat Nat Nat instHMul = f
  -- clear hm -- removing that assumption from context, to fully generalize
  rw [← hm]-- now this is false, so we need to revert it
  apply multPermute

theorem multPermute'' : ∀ (n m p : Nat), n * (m * p) = m * (n * p) :=
by
  intros n m p
  generalize hm : @HMul.hMul Nat Nat Nat instHMul = f
  clear hm
  revert f
  sorry
/---------------------------------------------------------------------------
A generalization of the theorem to any binary operation that is assoc & comm
---------------------------------------------------------------------------/
theorem fPermute :
∀ (f : Nat → Nat → Nat)
-- (f_assoc : ∀ (n m p : Nat),  f n (f m p) = f (f n m) p ) -- n (m p) = (n m) p
(gen_mul_assoc : ∀ (n m p : Nat),  f (f n m) p = f n (f m p)) -- n (m p) = (n m) p
(gen_mul_comm : ∀ (n m : Nat), f n m = f m n)
(n m p : Nat), f n (f m p) = f m (f n p) -- n (m p) = m (n p)
:= by

  intros f gen_mul_assoc gen_mul_comm n m p
  rw [← gen_mul_assoc]
  rw [gen_mul_comm n m]
  rw [gen_mul_assoc]
#print fPermute


theorem fPermute :
∀ (f : Nat → Nat → Nat)
-- (f_assoc : ∀ (n m p : Nat),  f n (f m p) = f (f n m) p ) -- n (m p) = (n m) p
(gen_mul_assoc : ∀ (n m p : Nat),  f (f n m) p = f n (f m p)) -- n (m p) = (n m) p
(gen_mul_comm : ∀ (n m : Nat), f n m = f m n)
(n m p : Nat), f n (f m p) = f m (f n p) -- n (m p) = m (n p)
:= by

  intros f gen_mul_assoc gen_mul_comm n m p
  rw [← gen_mul_assoc]
  rw [gen_mul_comm n m]
  rw [gen_mul_assoc]
#print fPermute

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

theorem gcdof5and7 : gcd 5 7 = 1 := by
  have neq5and7 : 5 ≠ 7 := by simp
  have p5 : Nat.Prime 5 := by simp
  have p7 : Nat.Prime 7 := by simp
  have copr := Nat.coprime_primes p5 p7
  apply Iff.mpr at copr
  exact copr (neq5and7)
#print gcdof5and7

theorem gcdofpand7 : Nat.Prime p → p ≠ 7 →  gcd p 7 = 1 := by
  intros pp neq
  have p7 : Nat.Prime 7 := by simp
  have copr := Nat.coprime_primes pp p7
  apply Iff.mpr at copr
  exact copr neq
#print gcdof5and7

theorem gcdofpand3 : ∀ p : ℕ, p ≠ 3 → Nat.Prime p → gcd p 3 = 1 := by
  intros p neq pp
  exact (Iff.mpr $ Nat.coprime_primes pp (Nat.prime_three)) neq
#print gcdofpand3

-- will gneralize saying, you need f (the generalized 3) to be prime
-- but really, you just need f (the generalized 3) to be coprime to p

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

theorem flt_example'' : 2^4 % (5 : ℤ) = (1 : ℤ) % (5 : ℤ):= by
  have hp2 : Nat.Prime 2 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have ne25 : 2 ≠ 5 := by norm_num
  have hcp := Iff.mpr (Nat.coprime_primes hp2 hp5) ne25
  have hcp' := Nat.Coprime.isCoprime hcp
  have flt := Int.ModEq.pow_card_sub_one_eq_one hp5 hcp'
  assumption
#print flt_example''


theorem flt_general (hp : Nat.Prime p) (hpn : IsCoprime a p) : a ^ (p - 1) % p = 1 := by
  sorry


/---------------------------------------------------------------------------
Given integers a and b, you can write their gcd as a linear combination of a and b
---------------------------------------------------------------------------/
theorem gcd_as_lin_comb : ∀ a b : ℤ, ∃ x y : ℤ, gcd a b = a*x + b*y := by
  intros a b
  exact exists_gcd_eq_mul_add_mul a b

/---------------------------------------------------------------------------
GCD of polynomials
---------------------------------------------------------------------------/
theorem gcd_as_lin_comb' : ∀ a b : ℤ, ∃ x y : ℤ, gcd a b = a*x + b*y := by
  intros a b
  exact exists_gcd_eq_mul_add_mul a b
#check Polynomial.degree_gcd_le_right

/---------------------------------------------------------------------------
Generalizing the theorem about GCDs from integers to polynomials
---------------------------------------------------------------------------/
-- example : True := by
--   let _gcdlincomb : ∀ a b : ℤ, ∃ x y : ℤ, gcd a b = a*x + b*y := by {intros a b; exact exists_gcd_eq_mul_add_mul a b}
--   autogeneralize _gcdlincomb a  -- adds _gcdlincomb.Gen to list of hypotheses
--   specialize _gcdlincomb.Gen ℝ 1 (0.5 : ℝ)
--   simp at _gcdlincomb.Gen