import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.GroupTheory.Subgroup.Basic
import TreeRewriteOrd
import TreeRewrite


example : True := by lib_apply trivial []



example : [PseudoMetricSpace α] → [PseudoMetricSpace β] → (f : α → β)
  → UniformContinuous f → Continuous f := by
  make_tree
  lib_rewrite Metric.uniformContinuous_iff [1,1,1,1,1,1,0,1]
  lib_rewrite Metric.continuous_iff [1,1,1,1,1,1,1]
  tree_apply [1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,0,1] [1,1,1,0,1]
  tree_apply [1,1,0,1] [1,1,1]

example [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β)
  : LipschitzWith 1 f → Continuous f := by
  make_tree
  lib_rewrite Metric.continuous_iff [1]
  lib_rewrite lipschitzWith_iff_dist_le_mul [0,1]
  simp
  tree_rewrite_ord [0,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  tree_rewrite_ord [1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,0,1]
  lib_rewrite_rev Set.mem_Ioo [1,1,1,1,1]
  lib_rewrite_rev Set.nonempty_def [1,1,1]
  lib_rewrite Set.nonempty_Ioo [1,1,1]
  tree_apply [1,1,0,1] [1,1,1]


lemma epsilon_lemma₁ : ∀ ε > (0 : ℝ), ∃ ζ > 0, ∃ η > 0, ε - η = ζ :=
  fun ε hε =>
    let hε2 : ε / 2 > 0 := div_pos hε (by simp)
    ⟨ε/2, hε2, ε/2, hε2, by ring⟩

lemma epsilon_lemma₂ : ∀ ε > (0 : ℝ), ∃ ζ > 0, ζ < ε :=
  fun ε hε =>
    ⟨ε/2, div_pos hε (by simp), by linarith [hε]⟩

example [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (F : ℕ → α → β)
  : (∀ n, Continuous (F n)) → TendstoUniformly F f Filter.atTop → Continuous f := by
  make_tree
  lib_rewrite Metric.tendstoUniformly_iff [1,0,1]
  lib_rewrite Filter.eventually_atTop [1,0,1,1,1,1]
  simp; make_tree
  lib_rewrite Metric.continuous_iff [1,1]
  lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  tree_rewrite_ord' [1,0,1,1,1,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,0,1]
  lib_apply add_lt_of_lt_sub_left [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  lib_rewrite epsilon_lemma₁ [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,0,1]
  tree_apply [1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,0,1]
  lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  lib_rewrite dist_comm [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1]
  tree_rewrite_ord [1,0,1,1,1,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1]
  lib_apply add_lt_of_lt_sub_right [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  lib_rewrite epsilon_lemma₁ [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,0,1]
  tree_apply [1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,0,1]

  lib_rewrite Metric.continuous_iff [0,1,1,1]
  tree_rewrite_ord [0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  lib_apply epsilon_lemma₂ [1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,1,1,0,1] [1,1,1,1,1,1,1,0,1]
  tree_apply [1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,0,1]
  lib_rewrite_rev max_le_iff [1,1,1,1,1,1]
  lib_apply refl [1,1,1,1,1,1]




variable [TopologicalSpace X]
open Set Function Filter TopologicalSpace Topology Uniformity
lemma seqCompactSpace_iff'' : IsSeqCompact (@Set.univ X) =
 ∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ (@Set.univ X)) → ∃ a ∈ (@Set.univ X), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  rfl

-- lemma seqCompactSpace_iff' : IsSeqCompact (@Set.univ X) ↔
--   ∀ ⦃x : ℕ → X⦄, ∃ a : X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
--   lib_rewrite seqCompactSpace_iff'' [0,1]
--   simp

#check IsCompact.isSeqCompact
-- example [TopologicalSpace X] : CompactSpace X → SeqCompactSpace X := by
--   make_tree
--   lib_rewrite seqCompactSpace_iff [1]
  -- lib_rewrite 
#check Subgroup.mk
#check Subgroup.closure
open BigOperators
#check Fin.sum_univ_succAbove
-- #eval ∏ s : Fin 6, (s+1 : ℕ)
#check Lean.Core.betaReduce
#check Lean.instantiateMVars
lemma induction {p : Nat → Prop} : (p 0 ∧ ∀ n, (p n → p (n + 1))) → ∀ n, p n := 
  fun ⟨zero, succ⟩ => Nat.rec zero succ

-- example : ∀ n : ℕ, n = (n * (n - 1) / 2) := by
--   make_tree
--   lib_intro Nat.rec
--   tree_apply [0,1,1,1,1,1] [1]
--   simp



example (n : Nat) : n = n := by
  induction n; rfl