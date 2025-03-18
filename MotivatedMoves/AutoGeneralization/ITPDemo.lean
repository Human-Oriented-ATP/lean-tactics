/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Demos of proof generalization tactic in Lean
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/
import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic

import MotivatedMoves.AutoGeneralization.Formalizations.irrationality_of_sqrts
import MotivatedMoves.AutoGeneralization.Formalizations.impossible_graphs

open Autogeneralize

open Real
open Lean Elab Tactic Meta Term Command

set_option linter.unusedVariables false
set_option pp.showLetValues false
-- set_option trace.ProofPrinting true

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Generalization of the proof that √17 is irrational
to the proof that the square root of any prime is irrational.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example : ∀ (p : ℕ), Nat.Prime p → Irrational √p := by

  /- Start with the theorem that √17 is irrational. -/
  let irrat_sqrt : Irrational (√17) := by  {apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 17 ∣ a := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 17 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 17 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 17 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 17] at h; have := Nat.Prime.ne_zero prime_seventeen; cases h with | inl => have b_div : 17 ∣ b := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 17 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (prime_seventeen) p_dvd_gcd | inr => apply this; assumption}

  /- Find the proof-based generalization of 17 to any prime, and add it as a theorem in the context. -/
  autogeneralize (17:ℕ) in irrat_sqrt

  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of robust generalization of _repeated_ uses of a constant.
Each occurrence of _17_ below generalizes separately.

Generalization of the proof that √17+17 is irrational
to the proof that √p+n is irrational for any prime p and nat n.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example: ∀ (p n : ℕ), Nat.Prime p → Irrational (√p + n) := by
  intros p n p_prime

  /- Start with the theorem that √17 is irrational. -/
  let irrat_sum_sqrt : Irrational (sqrt (17:ℕ)+17) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 17 ∣ a := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 17 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 17 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 17 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 17] at h; have := Nat.Prime.ne_zero prime_seventeen; cases h with | inl => have b_div : 17 ∣ b := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 17 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (prime_seventeen) p_dvd_gcd | inr => apply this; assumption}

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (17:ℕ) in irrat_sum_sqrt

  exact irrat_sum_sqrt.Gen p p_prime n

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of robust generalization of _dependent_ uses of a constant.
Generalizing the _2_ below automatically generalizes the _4_.

Generalization of the proof that |A ∪ B| ≤ 4 when |A|=2 and |B|=2
to the proof that |A ∪ B| ≤ n+m when |A|=n and |B|=m
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example : ∀ (n m : ℕ) (α : Type) [inst : Fintype α] [inst_2 : DecidableEq α] (A B : Finset α),
  A.card = n → B.card = m → (A ∪ B).card ≤ n+m:= by

  /- Start with the theorem that |A ∪ B| ≤ 4 when |A|=2 and |B|=2. -/
  let union_of_finsets (α : Type) [inst : Fintype α] [inst_2 : DecidableEq α] (A B : Finset α) (hA : A.card = 2) (hB : B.card = 2) : (A ∪ B).card ≤ 4 := by apply hA ▸ hB ▸ Finset.card_union_add_card_inter A B ▸ Nat.le_add_right _ _

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (2:ℕ) in union_of_finsets

  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Another demonstration of robust generalization of _dependent_ uses of a constant.
Generalizing the _4_ below automatically generalizes the _3_.

Generalization of the proof that no 4-vertex graph has degree sequence (1,3,3,3)
to the proof that no n-vertex graph has degree sequence (1, n-1, n-1, ..., n-1) when n > 2
(Note that when n=2, a graph with degree sequence (1,1) exists)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
example :
  ∀ (n : ℕ), 2 < n → ∀ (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj],
  (∃ v, G.degree v = 1 ∧ ∀ (w : Fin n), w ≠ v → G.degree w = n - 1) → False
:= by
  intro n hn

  /- Start with the theorem that no 4-vertex graph has degree sequence (1,3,3,3) -/
  let nonexistent_graph (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]: ¬(∃ (v : Fin 4), G.degree v = 1 ∧ ∀ w ≠ v, G.degree w = 3) := by { rintro ⟨v, v_deg, w_deg⟩; have hw_card : (Set.toFinset {w : Fin 4 | w ≠ v}).card = 3 := by {rw [Set.toFinset_card]; rw [Set.card_ne_eq]; rewrite [Fintype.card_fin]; rfl}; have neq_imp_adj : {w | w ≠ v} ⊆ {w | G.Adj v w} := by {rw [Set.setOf_subset_setOf]; intro w wneqv; apply max_deg_imp_adj_all; rewrite [Fintype.card_fin]; exact (w_deg w wneqv); exact wneqv.symm}; have v_deg_geq : 3 ≤ G.degree v := by {rw [← SimpleGraph.card_neighborFinset_eq_degree]; rw [← hw_card]; apply Finset.card_le_card; unfold SimpleGraph.neighborFinset; unfold SimpleGraph.neighborSet; rw [@Set.toFinset_subset_toFinset]; exact neq_imp_adj}; rw [v_deg] at v_deg_geq; exact Nat.not_lt.mpr v_deg_geq one_lt_three }

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (4:ℕ) in nonexistent_graph -- gen 4 first doesn't work b/c comp rule

  apply nonexistent_graph.Gen; exact Nat.lt_sub_of_add_lt hn
