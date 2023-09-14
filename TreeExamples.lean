import Mathlib.Topology.MetricSpace.Lipschitz
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


example [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (F : ℕ → α → β)
  : (∀ n, Continuous (F n)) → TendstoUniformly F f Filter.atTop → Continuous f := by
  make_tree
  lib_rewrite Metric.tendstoUniformly_iff [1,0,1]
  lib_rewrite Filter.eventually_atTop [1,0,1,1,1,1]
  simp; make_tree
  lib_rewrite Metric.continuous_iff [1,1]
  lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  tree_rewrite_ord' [1,0,1,1,1,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,0,1]
  lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1]
  lib_rewrite dist_comm [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1]
  tree_rewrite_ord [1,0,1,1,1,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1]
  
  lib_rewrite Metric.continuous_iff [0,1,1,1]
  sorry
lemma lem : ∀ x:ℝ, x > 0 →  x/4 + (x/4 + x/4) < x := by intros; linarith


example [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (F : ℕ → α → β)
: 
∀ b* : α⠀
∀ ε* : ℝ⠀
⬐ ε* > 0⠀
∃ ε_1• : ℝ⠀
⊢ 0 < ε_1•⠀
∀ a* : ℕ⠀
∃ ε_2• : ℝ⠀
⊢ 0 < ε_2•⠀
⬐ ∀ n* : ℕ⠀
  ∀ b'* : α⠀
  ∀ ε'* : ℝ⠀
  ⬐ ε'* > 0⠀
  ∃ δ• : ℝ⠀
  ⊢ δ• > 0⠀
  ∀ a* : α⠀
  ⬐ dist (a*) (b'*) < δ•⠀
  dist (F (n*) (a*)) (F (n*) (b'*)) < ε'*⠀
∀ a_1* : ℕ⠀
∃ δ• : ℝ⠀
⊢ δ• > 0⠀
∀ a_2* : α⠀
⬐ dist (a_2*) (b*) < δ•⠀
∃ b_1• : ℕ⠀
⊢ a_1* ≤ b_1•⠀
∃ b_2• : ℕ⠀
⊢ a* ≤ b_2•⠀
ε_2• + (dist (F (b_1•) (a_2*)) (F (b_2•) (b*)) + ε_1•) < ε*
:= by
  tree_rewrite_ord [1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,0,1]
  tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  lib_apply lem [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  tree_apply' [1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,1,0,1] [1,1,1,1,1,1,0,1]
  tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  tree_apply [1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,0,1]
  lib_rewrite_rev max_le_iff [1,1,1,1,1,1,1,1,1,1]
  lib_apply refl [1,1,1,1,1,1,1,1,1,1]
  intro _ _
  linarith
