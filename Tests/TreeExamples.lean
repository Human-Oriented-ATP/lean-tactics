import MotivatedMoves.Moves
import MotivatedMoves.GUI.MotivatedProofPanel

example : True := by lib_apply trivial []

example : [PseudoMetricSpace α] → [PseudoMetricSpace β] → (f : α → β)
  → UniformContinuous f → Continuous f := by
  make_tree
  lib_rewrite Metric.uniformContinuous_iff [1,1,1,0]
  lib_rewrite Metric.continuous_iff [1,1,1,1]
  make_tree
  tree_apply [1,1,1,0,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,1,0] [1,1,1,1,0]
  tree_apply [1,1,1,0] [1,1,1,1,1,0]
  tree_search

example [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) : 
  LipschitzWith 1 f → Continuous f := by
  make_tree
  lib_rewrite Metric.continuous_iff [1]
  lib_rewrite lipschitzWith_iff_dist_le_mul [0]
  make_tree
  tree_simp [0,1,2,1,1]
  tree_rewrite_ord [0,1,1] [1,1,1,1,1,1,1,1,2,0,1]
  tree_rewrite_ord [1,1,1,1,1,1,0] [1,1,1,1,1,1,1,2,0,1]
  lib_rewrite_rev Set.mem_Ioo [1,1,1]
  lib_rewrite_rev Set.nonempty_def [1,1]
  lib_rewrite Set.nonempty_Ioo [1,1]
  tree_apply [1,0] [1,1]


lemma epsilon_lemma₁ : ∀ ε > (0 : ℝ), ∃ ζ > 0, ∃ η > 0, ζ ≤ ε - η :=
  fun ε hε =>
    let hε2 : ε / 2 > 0 := div_pos hε (by simp)
    ⟨ε/2, hε2, ε/2, hε2, by ring_nf;rfl⟩

lemma epsilon_lemma₂ : ∀ ε > (0 : ℝ), ∃ ζ > 0, ζ < ε :=
  fun ε hε =>
    ⟨ε/2, div_pos hε (by simp), by linarith [hε]⟩

-- example [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (F : ℕ → α → β) : 
--   (∀ n, Continuous (F n)) → TendstoUniformly F f Filter.atTop → Continuous f := by
--   make_tree
--   lib_rewrite Metric.tendstoUniformly_iff [1,0]
--   make_tree
--   lib_rewrite Filter.eventually_atTop [1,0,1,1]
--   make_tree
--   try_lib_rewrite [1,1]
--   lib_rewrite Metric.continuous_iff [1,1]
--   make_tree
--   try_lib_rewrite_ord [1,1,1,1,1,1,1,1,1,0,1]
--   lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,2,0,1]
--   tree_rewrite_ord' [1,0,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,2,0,1,0,1]
--   lib_apply add_lt_of_lt_sub_left [1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   lib_rewrite_ord epsilon_lemma₁ [1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1]
--   tree_search
--   try_lib_rewrite_ord [1,1,1,1,1,1,1,1,1,1,1,1,0,1]
--   lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,1,1,1,2,0,1]
--   lib_rewrite dist_comm [1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1,1]
--   tree_rewrite_ord [1,0,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1,1]
--   try_lib_rewrite [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   lib_apply add_lt_of_lt_sub_right [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   lib_rewrite_ord epsilon_lemma₁ [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1]
--   tree_search
--   lib_rewrite Metric.continuous_iff [0,1]
--   make_tree
--   tree_rewrite_ord [0,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1]
--   tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,0] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0]
--   tree_search
--   lib_apply epsilon_lemma₂ [1,1,1,1,1,1,1,1,1]
--   tree_search
--   lib_rewrite_rev max_le_iff [1,1,1]
--   lib_apply refl [1,1,1]


variable [TopologicalSpace X]
open Set Function Filter TopologicalSpace Topology Uniformity
lemma seqCompactSpace_iff'' : IsSeqCompact (@Set.univ X) =
 ∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ (@Set.univ X)) → ∃ a ∈ (@Set.univ X), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  rfl


lemma cantor (X : Type u) (f : X → Set X) : ¬ Function.Surjective f := by
  tree_rewrite_def [2,1]
  make_tree
  tree_push_neg []
  lib_rewrite Set.ext_iff [1,1,2,1]
  tree_push_neg [1,1]

  lib_rewrite not_iff [1,1,1]
  sorry


example (X : Type u) (f : X → Set X) : ∃ b : X → Set X, ∃ c : X → X, ∀ a_1 : X, ∃ a_2 : X,
a_2 = c a_2 ∧ f a_1 = b a_2 := by
  make_tree
  lib_apply rfl [1,1,1,1,1]
  lib_apply rfl [1,1]


-- set_option tree.rememberNonempty true in



lemma simple_inverse : ∃ f : ℤ → ℤ, ∀ n, f (n+1) = n := by
  make_tree
  tree_name m [1,1,2,0,1,1]
  -- try_lib_rewrite [1,1,1,0]
  lib_rewrite_rev eq_sub_iff_add_eq [1,1,1,0]
  tree_rewrite [1,1,1,0] [1,1,1,1,2,1]
  lib_apply refl [1,1]


  
open BigOperators

lemma sum_add_distrib : ∀ n : ℕ, ∀ (f g : ℕ → ℕ), ∑ i in Finset.range n, (f i + g i) = (∑ i in Finset.range n, f i) + (∑ i in Finset.range n, g i) := by
  make_tree
  tree_induction []
  make_tree
  tree_simp [0,1,1]
  lib_rewrite Finset.sum_range_succ [1,1,1,1,2,1,0,1]
  lib_rewrite Finset.sum_range_succ [1,1,1,1,2,1,1]
  lib_rewrite Finset.sum_range_succ [1,1,1,1,2,0,1]
  tree_rewrite [1,0,1,1] [1,1,1,1,2,0,1,0,1]
  ring_nf
  tree_search


example : ∀ n : ℕ, ∑ i in Finset.range n, i = n * (n - 1) / 2 := by
  make_tree
  tree_induction []
  tree_simp [0]
  tree_search
  make_tree
  lib_rewrite Finset.sum_range_succ [1,1,2,0,1]
  tree_rewrite [1,0] [1,1,2,0,1,0,1]
  simp
  sorry -- this is a bit tricky to evaluate

example : p ∨ q → q ∨ p := by
  make_tree
  tree_induction []
  make_tree
  lib_apply Or.inl [1,1]
  tree_search
  lib_apply Or.inr [1]
  tree_search

example : p ∧ q → q ∧ p := by
  make_tree
  tree_induction []
  make_tree
  tree_search

example : ∀ r : ℚ, r^2 ≠ 2 := by
  make_tree
  tree_induction []
  make_tree
  lib_rewrite Rat.cast_mk' [1,1,1,1,2,0,1,0,1]
  tree_search'
  -- field_simp
  simp
  /-
  ∀ num⋆ : ℤ⠀
  ∀ den⋆ : ℕ⠀
  ⬐ den⋆ ≠ 0⠀
  ⬐ Nat.coprime (Int.natAbs (num⋆)) (den⋆)⠀
  (↑(num⋆) * (↑(den⋆))⁻¹) ^ 2 ≠ 2
  -/
  sorry