import Lean

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

theorem max_deg_imp_adj_all {V : Type} [Fintype V] {v : V} {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype (Gᶜ.neighborSet v)]  :
  G.degree v = Fintype.card V - 1 → ∀ w : V, w ≠ v → G.Adj w v := by
  intro hdeg w hne
  have hdeg_compl := G.degree_compl v
  rw [hdeg] at hdeg_compl

  simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le] at hdeg_compl
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_zero_iff] at hdeg_compl
  simp only [isEmpty_subtype, SimpleGraph.mem_neighborSet, SimpleGraph.compl_adj,  not_and, not_not] at hdeg_compl
  exact (hdeg_compl w hne.symm).symm


def one_lt_three : 1 < 3 := by exact Nat.one_lt_succ_succ 1

/- For any simple graph on 4 vertices, its degree sequence can't be {1,3,3,3}. -/
theorem impossible_graph (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]:
¬(∃ (v : Fin 4), G.degree v = 1 ∧ ∀ w ≠ v, G.degree w = 3) := by
  rintro ⟨v, v_deg, w_deg⟩

  have hw_card : (Set.toFinset {w : Fin 4 | w ≠ v}).card = 3 := by
    rw [Set.toFinset_card]
    rw [Set.card_ne_eq]
    rewrite [ Fintype.card_fin]
    rfl
    -- rfl
    -- simp only [Nat.reduceSub] -- or rfl

  have neq_imp_adj :  {w | w ≠ v} ⊆ {w | G.Adj v w} := by
    rw [Set.setOf_subset_setOf]
    intro w wneqv
    apply max_deg_imp_adj_all
    rewrite  [Fintype.card_fin]
    exact (w_deg w wneqv)
    exact wneqv.symm

  have v_deg_geq : 3 ≤ G.degree v  := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    rw [ ← hw_card]
    apply Finset.card_le_card
    unfold SimpleGraph.neighborFinset; unfold SimpleGraph.neighborSet
    rw [@Set.toFinset_subset_toFinset]
    exact neq_imp_adj

  rw [v_deg] at v_deg_geq

  -- have three_not_le_one : ¬ 3 ≤ 1  := Nat.not_ofNat_le_one
  -- simp at v_deg_geq; -- if we simp directly here, the proof doesn't autogen
  exact Nat.not_lt.mpr v_deg_geq one_lt_three
