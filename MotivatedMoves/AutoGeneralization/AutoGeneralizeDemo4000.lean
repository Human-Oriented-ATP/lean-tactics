/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Proof-based generalization.
Accounts for constants playing the same role in different places.
Accounts for generalizing constants to functions.
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Combinatorics.SimpleGraph.Basic
-- import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic4000
import MotivatedMoves.AutoGeneralization.library
open Autogeneralize library

open Real
open Lean Elab Tactic Meta Term Command

set_option linter.unusedVariables false
set_option pp.showLetValues false
-- set_option pp.explicit true
-- set_option profiler true

-- variable (V' : Type) (G' : SimpleGraph V') (v' : V') [DecidableRel G'.Adj] [DecidableRel G'ᶜ.Adj]
-- instance [Fintype V'] : Fintype (G'.neighborSet v') := by
--   apply Subtype.fintype _
-- instance [Fintype V'] : Fintype (G'ᶜ.neighborSet v') := by
--   apply Subtype.fintype _

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING PROOFS OF DEGREE SEQUENCES
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example : True := by
  -- Given any simple graph on 4 vertices, its degree sequence can't be {1,3,3,3}.
  let impossible_graph (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]: ¬(∃ (v : Fin 4), G.degree v = 1 ∧ ∀ w ≠ v, G.degree w = 3) := by { have max_deg_imp_adj_all {V : Type} [Fintype V] {v : V} {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype (Gᶜ.neighborSet v)] : G.degree v = Fintype.card V - 1 → ∀ w : V, w ≠ v → G.Adj w v := by { intro hdeg w hne; have hdeg_compl := G.degree_compl v; rw [hdeg] at hdeg_compl; simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le] at hdeg_compl; rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_zero_iff] at hdeg_compl; simp only [isEmpty_subtype, SimpleGraph.mem_neighborSet, SimpleGraph.compl_adj, not_and, not_not] at hdeg_compl; exact (hdeg_compl w hne.symm).symm }; rintro ⟨v, hv_deg, hw_deg⟩; have hw_adj_all : ∀ w ≠ v, G.Adj v w := λ w wneqv => (max_deg_imp_adj_all (hw_deg w wneqv) v wneqv.symm); have hw_card : (Set.toFinset {w : Fin 4 | w ≠ v}).card = 3 := by { rw [@Set.toFinset_card]; simp }; have neq_imp_adj : {w | w ≠ v} ⊆ {w | G.Adj v w} := hw_adj_all; have hv_deg_geq : 3 ≤ G.degree v := by { rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hw_card]; apply Finset.card_le_card; rw [← Set.toFinset_subset_toFinset] at neq_imp_adj; exact neq_imp_adj }; rw [hv_deg] at hv_deg_geq; contradiction }
  -- autogeneralize (3:ℕ) in impossible_graph
  trivial

#exit

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING PROOFS OF SET SUMS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

variable {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α]


example : True := by
  let union_of_finsets (A B : Finset α) (hA : A.card = 2) (hB : B.card = 2)
  : (A ∪ B).card ≤ 4
  := --id $
  by
    have h1 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
    rwa [hA, hB] at h1
    --have h2 : A.card + B.card = 4 := by simp [hA, hB]
    --rwa [h2] at h1

  autogeneralize (4:ℕ) in union_of_finsets
  autogeneralize (2:ℕ) in union_of_finsets.Gen

  simp

/--
Fabian's example:
  "hyp" is a proof that DOES NOT depend on the fact that x ≠ 0 to prove P  (even though x ≠ 0 is proven at some point on the proof)
  and therefore generalizes to
  "hyp.Gen" which is a proof that ∀ x, P x
-/
def P (x : ℝ) := ∀ y : ℝ, y = 0 → x * y = 0
example : ∀ x : ℝ, P x := by
  let hyp :  ∀ y : ℝ, y = 0 → 2 * y = 0 := by {intro y h; have twoneq : (2:ℝ) ≠ 0 := two_ne_zero; apply mul_eq_zero_of_right; apply h};
  autogeneralize 2 in hyp -- generalizes to a statement that works for all x:ℝ, not requiring x ≠ 0
  assumption

/--
Fabian's example:
  "hyp" is a proof that DOES depend on the fact that x ≠ 0 to prove P
  and therefore generalizes to
  "hyp.Gen" which is a proof that ∀ x, x ≠ 0 → P x
-/
def P' (x : ℝ) := ∀ y : ℝ, x * y = 0 → y=0
example : ∀ x : ℝ, NeZero x → P' x := by
  let hyp :  ∀ y : ℝ, 1 * y = 0 → y = 0 := by {intro y h;  have oneneq : (1:ℝ) ≠ 0 :=  neZero_iff.mp Complex.instNeZeroRealInstZeroRealOfNatToOfNat1InstOneReal;  apply eq_zero_of_ne_zero_of_mul_left_eq_zero oneneq h;};
  autogeneralize 1 in hyp
  assumption


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING PROOFS OF IRRATIONALITY.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--
Example:
sqrt(2) is irrational generalizes to sqrt(prime) is irrational
-/
example : Irrational (sqrt 3) := by
  let sum_irrat : Irrational (sqrt (2:ℕ)) := by {apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize_basic (2:ℕ) in sum_irrat
  specialize sum_irrat.Gen 3 (Nat.prime_three)
  assumption

/--
Example of a naive, over-specialized generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+prime is irrational
-/
example : Irrational (sqrt 3 + 3) := by
  let sum_irrat : Irrational (sqrt (2:ℕ) + 2) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize_basic (2:ℕ) in sum_irrat
  specialize sum_irrat.Gen 3 (Nat.prime_three)
  assumption

/--
Example of a better, constant-aware generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+nat is irrational
-/
example : Irrational (sqrt 3 + 6) := by
  let sum_irrat : Irrational (sqrt (2:ℕ) + 2) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize (2:ℕ) in sum_irrat
  specialize sum_irrat.Gen 3 (Nat.prime_three) 6
  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING SIZES OF SETS.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

variable {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α]

/--
Example of a naive, over-specialized generalization:
This generalizes all four 3s in the same way. (There are four 3s in the theorem statement.  2 are related, 2 not.)
-/
example : Fintype.card α = 4 → Fintype.card β = 4 → Fintype.card (α → β) = 4 ^ 4 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize_basic 3 in fun_set
  specialize @fun_set.Gen 4
  assumption

/--
Example of a better, constant-aware generalization:
Generalizes the pairs of 3s separately.
-/
example : Fintype.card α = 4 → Fintype.card β = 5 → Fintype.card (α → β) = 5 ^ 4 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize 3 in fun_set
  specialize @fun_set.Gen 4 5
  assumption

/--
Demonstration of functionality to generalize at specified occurrences.
This generalizes just the first pair of 3s.
-/
example : Fintype.card α = 4 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 4 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize 3 in fun_set at occurrences [1]
  specialize @fun_set.Gen 4
  assumption

/--
Demonstration of functionality to generalize at specified occurrences.
This generalizes just the second pair of 3s.
-/
example : Fintype.card α = 3 → Fintype.card β = 4 → Fintype.card (α → β) = 4 ^ 3 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize 3 in fun_set at occurrences [2]
  specialize @fun_set.Gen 4
  assumption


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING FUNCTIONS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--
Generalizing an operator that only requires commutativity.
-/

example :  1 + 2 = 2 + 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm
  autogeneralize_basic Mul.mul in mult_comm -- generalize all
  specialize mult_comm.Gen Add.add Nat.add_comm 1 2
  assumption

example :  1 + 2 = 2 + 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm
  autogeneralize Mul.mul in mult_comm -- generalize all, separately
  specialize mult_comm.Gen Add.add Add.add Nat.add_comm 1 2
  assumption

example :  1 * 2 = 2 * 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm
  autogeneralize (HMul.hMul) in mult_comm at occurrences [1] -- generalize at first occurrence
  specialize mult_comm.Gen Mul.mul Nat.mul_comm 1 2
  assumption

example :  1 + 2 = (2 + 1)*1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = (m * n) * 1 :=  by {intros a b; rw [Nat.mul_one]; apply Nat.mul_comm}
  autogeneralize (HMul.hMul) in mult_comm at occurrences [1 3] -- generalize just at first and third occurrences, separately
  specialize mult_comm.Gen Add.add Add.add (Nat.mul_one) Nat.add_comm 1 2 -- ideally shouldnt say "mul_one"
  assumption

example :  1 * 2 = (2 * 1)*1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = (m * n) * 1 :=  by {intros a b; rw [Nat.mul_one]; apply Nat.mul_comm}
  autogeneralize (HMul.hMul) in mult_comm at occurrences [1 2] -- generalize just at first and second occurrences, separately
  specialize mult_comm.Gen Mul.mul Mul.mul (Nat.mul_one) Nat.mul_comm 1 2
  assumption

/--
Generalizing an operator that requires commutativity and associativity.
Generalizes all instances of * in the same way.
-/
example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let mult_permute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize_basic Mul.mul in mult_permute
  specialize mult_permute.Gen (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption

/--
Generalizing an operator that requires commutativity and associativity.
Generalizes all instances of * separately.
-/
example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let mult_permute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize Mul.mul in mult_permute
  specialize mult_permute.Gen (.+.) (.+.) (.+.) (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING WITH COMPUTATION RULES
Demonstration that compatible proofs must use deduction rules, not computation rules
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--
An example where only deduction rules are used, so the proof generalizes.
-/
example := by
  let two_times_three_is_even : Even (2*3) := by {unfold Even; apply Exists.intro 3; rw [two_mul]}
  autogeneralize 3 in two_times_three_is_even
  assumption

/--
An example where "3" doesn't show up in the proof term (due to use of the computation rule reduceMul), so the proof doesn't generalize.
-/
theorem six_is_even : Even 6 := by {unfold Even; use 3}
example := by
  let two_times_three_is_even : Even (2*3) := by
    simp only [Nat.reduceMul]; apply six_is_even
  -- autogeneralize 3 in two_times_three_is_even -- throws error b/c of computation rule
  assumption
