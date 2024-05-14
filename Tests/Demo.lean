import MotivatedMoves.Moves

/-- Cantor's Theorem in Set Theory -/
theorem Cantor : (X : Type u) → (f : X → Set X) → ¬ f.Surjective := by
motivated_proof
  tree_rewrite_def [1, 1, 1, 2]
  tree_push_neg [1, 1]
  lib_rewrite [1, 1, 1, 2, 0, 1] Set.ext_iff [1, 1, 1, 1, 1, 2]
  tree_push_neg [1, 1, 1, 1]
  lib_rewrite [1, 1, 2, 0, 1] not_iff [1, 1, 1, 1, 1]
  unify_forall_exists [1, 1, 1]
  lib_apply refl [1, 1, 1, 1, 2]

/-- The sum of continuous functions is continuous. -/
example : ∀ (α : Type u), [PseudoMetricSpace α] →
  ∀ f g : α → ℝ, Continuous f → Continuous g →
  Continuous (f + g) := by
motivated_proof
  lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] Metric.continuous_iff [1, 1, 1, 1, 1, 1, 2]
  lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] Metric.continuous_iff [1, 1, 1, 1, 1, 0, 2]
  lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] Metric.continuous_iff [1, 1, 1, 1, 0, 2]
  lib_rewrite [1, 1, 1, 1, 1, 1, 2, 0, 1] Pi.add_apply [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 0, 1]
  lib_rewrite [1, 1, 1, 1, 1, 1, 2, 0, 1] Pi.add_apply [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
  lib_rewrite [1, 1, 2, 0, 1] Real.dist_eq [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
  lib_rewrite [1, 1, 1, 1, 1, 1, 2, 1] sub_add_sub_comm [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
  lib_rewrite_ord [1, 1, 1, 1] abs_add [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
  lib_rewrite [1, 1, 2, 1] Real.dist_eq [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 0, 1]
  lib_rewrite [1, 1, 2, 1] Real.dist_eq [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
  tree_rewrite_ord [1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 0, 1]
  tree_rewrite_ord [1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
  lib_apply  [1, 1, 1, 1, 1, 1, 0] exists_add_lt_and_pos_of_lt [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
  lib_rewrite [1, 1, 1, 1, 1, 2, 1] lt_min_iff [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  tree_apply [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
  lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] lt_min_iff [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
  tree_search
  lib_rewrite [1, 1, 2, 0, 1] and_comm [1, 1, 1]
  lib_rewrite [1, 1, 1, 1, 1, 2, 1] Set.mem_Ioo [1, 1, 1]
  lib_rewrite [1, 1, 2, 1] Set.nonempty_def [1, 1]
  lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] Set.nonempty_Ioo [1, 1, 2]
  tree_apply [1, 0, 2] [1, 1, 2]
