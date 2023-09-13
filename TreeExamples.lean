import Mathlib.Topology.MetricSpace.Lipschitz
import TreeRewriteOrd
import TreeRewrite


example : True := trivial



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

#check dist_comm
#check dist_triangle
lemma impswap (p q r : Prop) : p → q → r ↔ q → p → r := imp.swap
abbrev Imp p q := p → q 
lemma exswap {α : Type u} (p : α → Prop) (q : Prop) : (∃ a, q → p a) → Imp q (∃ a, p a) :=
  fun ⟨a, h⟩ hq => ⟨a, h hq⟩ 
lemma andswap {α : Prop} (p : Prop) (q : Prop) : (a ∧ (q → p)) → Imp q (a ∧ p) :=
  fun ⟨a, h⟩ hq => ⟨a, h hq⟩ 

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
  lib_rewrite imp_forall_iff []
  lib_rewrite imp_forall_iff [1,1]
  lib_rewrite impswap [1,1,1,1]
  lib_apply exswap [1,1,1,1,1]
  simp
  lib_apply andswap [1,1,1,1,1,1,1]
  lib_rewrite imp_forall_iff [1,1,1,1,1,1,1,1,1]
  simp; make_tree
  tree_rewrite_ord [1,1,1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  -- tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  sorry
#check Metric.tendstoUniformly_iff
#check Filter.eventually_atTop
-- variable [PseudoMetricSpace α]

-- #check TendstoUniformly (fun (_ : Nat) => @id α) id .atTop

-- #check Filter.atTop

-- #synth Top (Filter ℕ)