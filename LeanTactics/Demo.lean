import LeanTactics.MotivatedProofList

/- `Cantor's Theorem` in `Set Theory` -/
theorem Cantor : (X : Type u) → (f : X → Set X) → ¬ f.Surjective := by
motivated_proof
tree_rewrite_def [1, 1, 2, 1]
tree_push_neg [1, 1, 2]
lib_rewrite [1, 1, 1, 2, 0, 1] Set.ext_iff [1, 1, 1, 1, 2, 1]
tree_push_neg [1, 1, 1, 1, 2]
lib_rewrite [1, 1, 2, 0, 1] not_iff [1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 1, 2, 1] Set.mem_compl_iff [1, 1, 1, 1, 1, 2, 0, 1]
unify_forall_exists [1, 1, 1]
lib_apply refl [1, 1, 1, 1, 2]




