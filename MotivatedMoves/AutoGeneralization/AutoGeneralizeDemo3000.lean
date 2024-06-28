/-
Proof-based generalization
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic3000
open Autogeneralize

open Real
open Lean Elab Tactic Meta Term Command

-- Uncomment below to hide proofs of "let" statements in the LeanInfoview
set_option pp.showLetValues false
-- set_option pp.explicit true
-- set_option profiler true

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example:
sqrt(2) is irrational generalizes to sqrt(prime) is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
example : ¬∃x : ℚ, x^2 = ((3:ℕ):ℤ) := by
  let _irr : ¬∃x : ℚ, x^2 = ((3:ℕ):ℤ) := by
    intro h

    have assume_pos : (∃q : ℚ, q^2 = (3:ℕ)) → ∃q : ℚ,  0 ≤ q ∧ q^2 = (3:ℕ) := by
      intros gen
      obtain ⟨q, hq⟩ := gen
      by_cases h : 0 > q

      use -q
      constructor
      linarith
      simp [hq]

      use q
      simp at h
      exact ⟨h, hq⟩

    apply assume_pos at h
    clear assume_pos

    obtain ⟨x, ⟨x_pos, hx⟩ ⟩ := h
    have ab := (Iff.mp Rat.eq_iff_mul_eq_mul) hx
    simp at ab
    have ab_copr := x.reduced

    have asq : (x*x).num = x.num*x.num := by rw [Rat.mul_self_num]

    have bsq : (x*x).den = x.den*x.den := by rw [Rat.mul_self_den]
    ring_nf at asq
    ring_nf at bsq
    rw [ab, bsq] at asq
    clear bsq ab

    have num_pos : 0 ≤ x.num := Rat.num_nonneg_iff_zero_le.mpr x_pos
    clear x_pos
    have num_is_nat: x.num = x.num.natAbs :=
      Int.eq_natAbs_of_zero_le num_pos
    rw [num_is_nat] at asq
    norm_cast at asq
    clear num_is_nat num_pos

    have num_sq_even : (3:ℕ) ∣ (Int.natAbs x.num)^2  := by
      apply (Iff.mpr dvd_iff_exists_eq_mul_right)
      use (x.den^2)
      apply Eq.symm
      rw [asq]
    have num_abs_even : (3:ℕ) ∣ (Int.natAbs x.num) := by
      apply Nat.Prime.dvd_of_dvd_pow (Nat.prime_three) num_sq_even
    have num_is_2k : ∃ k,  (Int.natAbs x.num)= (3:ℕ)*k := by
      apply (Iff.mp dvd_iff_exists_eq_mul_right)
      exact num_abs_even
    clear num_sq_even

    obtain ⟨k, hk⟩ := num_is_2k
    rw [hk] at asq
    clear hk

    simp [mul_pow, mul_comm k, mul_assoc, mul_left_cancel, mul_right_cancel ] at asq
    rw [← Nat.pred_succ 2] at asq
    rw [Nat.succ_eq_add_one] at asq
    rw [Nat.pred_eq_sub_one] at asq
    rw [pow_succ 3 1] at asq
    rw [mul_assoc] at asq
    simp [mul_left_cancel] at asq

    have den_sq_even : (3:ℕ) ∣ (x.den^2)  := by
      apply (Iff.mpr dvd_iff_exists_eq_mul_right)
      use (k^2)
    have den_even : (3:ℕ) ∣ x.den := by
      apply Nat.Prime.dvd_of_dvd_pow (Nat.prime_three) den_sq_even
    clear den_sq_even k asq

    unfold Nat.Coprime at ab_copr

    have two_dvd_gcd : (3:ℕ) ∣ gcd (Int.natAbs x.num) x.den := by
      apply Iff.mpr (dvd_gcd_iff _ _ _)
      constructor
      exact num_abs_even
      exact den_even
    clear num_abs_even den_even

    simp [← gcd_eq_nat_gcd] at ab_copr
    rw [ab_copr] at two_dvd_gcd
    have := Nat.dvd_one.mp two_dvd_gcd
    linarith

  autogeneralize_basic (3:ℕ ) in _irr -- adds _sqrt2Irrational.Gen to list of hypotheses
  -- a → (b → (a → conclusion))
  specialize _irr.Gen (Int.prime_three) (Int.prime_three)
  exact _irr.Gen



/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example:
sqrt(2) is irrational generalizes to sqrt(prime) is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
example : Irrational (Real.sqrt 3) := by
  let _sqrt2Irrational : Irrational (Real.sqrt (2: ℕ)) := by apply Nat.prime_two.irrational_sqrt
  autogeneralize_basic (2:ℕ) in _sqrt2Irrational -- adds _sqrt2Irrational.Gen to list of hypotheses

  specialize _sqrt2Irrational.Gen 3 (Nat.prime_three)
  assumption

















/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example of a naive, over-specialized generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+prime is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
example : Irrational (Real.sqrt 3 + 3) := by
  let _sum_irrat : Irrational (Real.sqrt (2:ℕ) + (2:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}
  autogeneralize_basic (2:ℕ) in _sum_irrat

  specialize _sum_irrat.Gen 3 (Nat.prime_three)
  assumption














/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Example of a better, constant-aware generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+nat is irrational
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
example : Irrational (Real.sqrt 3 + 6) := by
  let _sum_irrat : Irrational (Real.sqrt (2:ℕ) + (2:ℕ)) := by {apply Irrational.add_nat; apply Nat.prime_two.irrational_sqrt}
  autogeneralize (2:ℕ) in _sum_irrat
  autogeneralize (2:ℕ) in _sum_irrat.Gen

  specialize _sum_irrat.Gen.Gen 6 3 (Nat.prime_three)
  -- specialize _sum_irrat.Gen 3 (Nat.prime_three)
  assumption









/- --------------------------------------------------------------------------
DEMO OF HARD CASE -- four 3s in the theorem statement.  2 are related, 2 not.
-------------------------------------------------------------------------- -/
example :
  ∀ {α β : Type} [Fintype α] [Fintype β]  [DecidableEq α], Fintype.card α = 4 → Fintype.card β = 4 → Fintype.card (α → β) = 4 ^ 4 :=
by
  let _fun_set : ∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
                  Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := fun {α β} [Fintype α] [Fintype β] [DecidableEq α] fa fb => Eq.mpr (id (congrArg (fun _a => _a = 3 ^ 3) Fintype.card_fun)) (Eq.mpr (id (congrArg (fun _a => Fintype.card β ^ _a = 3 ^ 3) fa)) (Eq.mpr (id (congrArg (fun _a => _a ^ 3 = 3 ^ 3) fb)) (Eq.refl (3 ^ 3))))
  autogeneralize_basic 3 in _fun_set
  specialize @_fun_set.Gen 4
  assumption












/- --------------------------------------------------------------------------
DEMO OF HARD CASE -- four 3s in the theorem statement.  2 are related, 2 not.
-------------------------------------------------------------------------- -/
example :
  ∀ {α β : Type} [Fintype α] [Fintype β]  [DecidableEq α], Fintype.card α = 4 → Fintype.card β = 5 → Fintype.card (α → β) = 5 ^ 4 :=
by
  let _fun_set : ∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
                  Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := fun {α β} [Fintype α] [Fintype β] [DecidableEq α] fa fb => Eq.mpr (id (congrArg (fun _a => _a = 3 ^ 3) Fintype.card_fun)) (Eq.mpr (id (congrArg (fun _a => Fintype.card β ^ _a = 3 ^ 3) fa)) (Eq.mpr (id (congrArg (fun _a => _a ^ 3 = 3 ^ 3) fb)) (Eq.refl (3 ^ 3))))

  autogeneralize 3 in _fun_set
  autogeneralize 3 in _fun_set.Gen

  specialize @_fun_set.Gen.Gen 5 4

  assumption










/- --------------------------------------------------------------------------
DEMO OF HARD & EASY CASE -- The formula for the distance between any two points in ℝ² -- autogeneralize works fine when there's only one instance of what to generalize
-------------------------------------------------------------------------- -/

example :  ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) :=
by
  let _distance : ∀ (x y : EuclideanSpace (ℝ:Type) (Fin 2)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq.{0,0} x y

  autogeneralize 2 in _distance  -- says this formula works for any f-dimensional space as long as distance is given by (∑ i, dist (x i) (y i) ^ f)

  intros x y
  specialize _distance.Gen 3 (EuclideanSpace.dist_eq) x y -- x is not a member of a 3-dimensional space such that the distance is given by (∑ i, dist (x i) (y i) ^3)
  assumption

example :  ∀ (x y : EuclideanSpace ℝ (Fin 4)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := by
  let _distance : ∀ (x y : EuclideanSpace ℝ (Fin 3)), dist x y = sqrt (Finset.sum Finset.univ fun i => dist (x i) (y i) ^ 2) := fun x y => EuclideanSpace.dist_eq x y
  autogeneralize 3 in _distance

  intros x y
  specialize _distance.Gen 4 x y
  assumption
/---------------------------------------------------------------------------
Analogizing a theorem about an operator that uses commutativity and associativity
---------------------------------------------------------------------------/
example :  1 * 2 = 2 * 1 := by
  -- let _multComm :  ∀ (n m : ℕ), n * m = m * n := by {intros n m; apply Nat.mul_comm}
  let _multComm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm

  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multComm  -- (.*.) -- adds multPermute.Gen to list of hypotheses

  specialize _multComm.Gen ( fun a b => b * a) (fun _ _ => rfl) 1 2
  assumption


example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let _multPermute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute  -- adds multPermute.Gen to list of hypotheses
  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute.Gen
  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute.Gen.Gen
  autogeneralize (@HMul.hMul ℕ ℕ  ℕ instHMul) in _multPermute.Gen.Gen.Gen

  specialize _multPermute.Gen.Gen.Gen.Gen (.+.) (.+.) (.+.) (.+.) (.+.) (.+.) Nat.add_assoc (.+.) Nat.add_comm Nat.add_assoc 1 2 3
  assumption
