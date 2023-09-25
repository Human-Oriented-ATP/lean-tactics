import TreeMoves.TreeRewriteOrd
import TreeMoves.TreeRewrite
import TreeMoves.TreeInduction
import TreeMoves.TreeNormalize
import TreeMoves.TreeSearch

import TreeMoves.PrintTree
import LeanTactics.DynamicButtonList


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
  tree_simp [0,1,1,1]
  tree_rewrite_ord [0,1,1] [1,1,1,1,1,1,1,1,0,1]
  tree_rewrite_ord [1,1,1,1,1,1,0] [1,1,1,1,1,1,1,0,1]
  lib_rewrite_rev Set.mem_Ioo [1,1,1]
  lib_rewrite_rev Set.nonempty_def [1,1]
  lib_rewrite Set.nonempty_Ioo [1,1]
  tree_apply [1,0] [1,1]


lemma epsilon_lemma₁ : ∀ ε > (0 : ℝ), ∃ ζ > 0, ∃ η > 0, ε - η = ζ :=
  fun ε hε =>
    let hε2 : ε / 2 > 0 := div_pos hε (by simp)
    ⟨ε/2, hε2, ε/2, hε2, by ring⟩

lemma epsilon_lemma₂ : ∀ ε > (0 : ℝ), ∃ ζ > 0, ζ < ε :=
  fun ε hε =>
    ⟨ε/2, div_pos hε (by simp), by linarith [hε]⟩

example [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (F : ℕ → α → β) : 
  (∀ n, Continuous (F n)) → TendstoUniformly F f Filter.atTop → Continuous f := by
  make_tree
  lib_rewrite Metric.tendstoUniformly_iff [1,0]
  make_tree
  lib_rewrite Filter.eventually_atTop [1,0,1,1]
  lib_rewrite Metric.continuous_iff [1,1]
  make_tree
  -- try_lib_rewrite_ord [1,1,1,1,1,1,1,1,1,0,1]
  lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,0,1]
  tree_rewrite_ord' [1,0,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,0,1,0,1]
  lib_apply add_lt_of_lt_sub_left [1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  lib_rewrite epsilon_lemma₁ [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  tree_search
  lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  lib_rewrite dist_comm [1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1]
  tree_rewrite_ord [1,0,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1]
  lib_apply add_lt_of_lt_sub_right [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  lib_rewrite epsilon_lemma₁ [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  tree_search
  lib_rewrite Metric.continuous_iff [0,1]
  make_tree
  tree_rewrite_ord [0,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,0] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0]
  tree_search
  lib_apply epsilon_lemma₂ [1,1,1,1,1,1,1,1,1]
  tree_search
  lib_rewrite_rev max_le_iff [1,1,1]
  lib_apply refl [1,1,1]


variable [TopologicalSpace X]
open Set Function Filter TopologicalSpace Topology Uniformity
lemma seqCompactSpace_iff'' : IsSeqCompact (@Set.univ X) =
 ∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ (@Set.univ X)) → ∃ a ∈ (@Set.univ X), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  rfl



open BigOperators

lemma sum_add_distrib : ∀ n : ℕ, ∀ (f g : ℕ → ℕ), ∑ i in Finset.range n, (f i + g i) = (∑ i in Finset.range n, f i) + (∑ i in Finset.range n, g i) := by
  make_tree
  tree_induction []
  make_tree
  tree_simp [0,1,1]
  lib_rewrite Finset.sum_range_succ [1,1,1,1,1,0,1]
  lib_rewrite Finset.sum_range_succ [1,1,1,1,1,1]
  lib_rewrite Finset.sum_range_succ [1,1,1,1,0,1]
  tree_rewrite [1,0,1,1] [1,1,1,1,0,1,0,1]
  ring_nf
  tree_search


example : ∀ n : ℕ, ∑ i in Finset.range n, i = n * (n - 1) / 2 := by
  make_tree
  tree_induction []
  tree_simp [0]
  tree_search
  make_tree
  lib_rewrite Finset.sum_range_succ [1,1,0,1]
  tree_rewrite [1,0] [1,1,0,1,0,1]
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
  lib_rewrite Rat.cast_mk' [1,1,1,1,0,1,0,1]
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

-- example (a b c : Int) : a + b + c = a + (b + c) := by
--   try_lib_rewrite [0,1]

#exit
#check Finset.sum_range_id

example (N : ℕ) : ∑ n in Finset.range N, n  = N * (N - 1) / 2 := by
  try_lib_rewrite [0,1]

example (N : ℕ) : ∑ n in Finset.range N, (a + b)  = N * (N - 1) / 2 := by
  try_lib_rewrite [0,1]

#exit
example : ∃ x, x = x := by
  make_tree
  try_lib_apply [1]

-- #print prefix Aesop.Check.script
#check Aesop.Check.script.sizeOf_spec
#check Aesop.Check.all.sizeOf_spec

#check Nat.Coprime
#check Exists.rec
example : (∃ x:Nat, 1=1) → True := by
  make_tree
  tree_induction []



#exit
example (hf : (mulSupport f).Finite) (hg : (mulSupport g).Finite) : 
  ( ∏ᶠ i, f i * g i )= (∏ᶠ i, (f i + 1)) * (∏ᶠ i : α, g i) := by
    try_lib_rewrite [0,1]
