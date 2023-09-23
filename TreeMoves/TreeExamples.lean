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


-- some weird behaviour going on here:

-- elab "lib_intro" h:ident : tactic =>
--   Tree.workOnTree (m := Lean.Meta.MetaM) fun tree => do
--   let (h, p) ← Tree.getConstAndTypeFromIdent h
--   -- let p ← Tree.makeTree p
--   return {
--     newTree := Lean.mkApp2 (.const ``Tree.Imp []) p tree
--     proof := Lean.mkApp3 (.const ``Tree.imp []) p tree h
--   }
-- open Tree in
-- def Nat.rec' : Forall _ fun motive : ℕ → Prop => Imp (motive 0) $ Imp ((n : ℕ) → motive n → motive (n+1)) $ Forall _ motive :=
--   @Nat.rec
-- open Tree in
-- def Nat.rec'' : Forall _ fun motive : ℕ → Prop => Imp (motive 0) $ Imp ((n : ℕ) → motive n → motive (n+1)) $ (t : ℕ) → motive t :=
--   @Nat.rec

-- example : ∀ n : ℕ, n = (n * (n - 1) / 2) := by
--   make_tree
--   lib_intro Nat.rec'
--   tree_apply [0,1,1,1,1,1] [1]
--   sorry

open BigOperators

lemma sum_add_distrib : ∀ n : ℕ, ∀ (f g : Fin n → ℕ), ∑ i : Fin n, (f i + g i) = (∑ i : Fin n, f i) + (∑ i : Fin n, g i) := by
  make_tree
  tree_induction []
  make_tree
  tree_simp [0,1,1]
  lib_rewrite Fin.sum_univ_castSucc [1,1,1,1,1,0,1]
  lib_rewrite Fin.sum_univ_castSucc [1,1,1,1,1,1]
  lib_rewrite Fin.sum_univ_castSucc [1,1,1,1,0,1]
  tree_rewrite [1,0,1,1] [1,1,1,1,0,1,0,1]
  ring_nf
  tree_search


example : ∀ n : ℕ, ∑ i : Fin n, (i : Int) = (n * (n - 1) / 2) := by
  make_tree
  tree_induction []
  tree_simp [0]
  tree_search
  make_tree
  lib_rewrite Fin.sum_univ_castSucc [1,1,0,1]
  tree_rewrite [1,0] [1,1,0,1,0,1]
  norm_cast
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

#check finsum_sub_distrib
-- #exit

-- example (a b c : Int) : a + b + c = a + (b + c) := by
--   try_lib_rewrite [0,1]

open BigOperators

variable {M α : Type*} [Field M] {f g : α → M} (a : α)
-- set_option pp.all true in 


#exit
open Tree DiscrTree Lean Meta Elab Tactic
def librarySearchApply' (goalPos : List Nat) (tree : Expr) : MetaM (Array (Array (Name × AssocList SubExpr.Pos Widget.DiffTag × String) × Nat)) := do
  let discrTrees ← getLibraryLemmas
  let (goalPath, []) := posToPath goalPos tree | throwError "cannot apply in a subposition"
  let results := if pathToPol goalPath then
    (← getSubExprUnify discrTrees.1.apply tree goalPath []) ++ (← getSubExprUnify discrTrees.2.apply tree goalPath [])
  else
    (← getSubExprUnify discrTrees.1.apply_rev tree goalPath []) ++ (← getSubExprUnify discrTrees.2.apply_rev tree goalPath [])

  -- let results ← filterLibraryResults results fun {name, path, pos, ..} => do
  --   try
  --     _ ← applyUnbound name (fun hyp _goalPath => return (← makeTreePath path hyp, path, pos)) goalPos treeApply tree
  --     return true
  --   catch _ =>
  --     return false
  let results := results[:10].toArray

  return results.map $ Bifunctor.fst $ Array.map fun {name, path, pos, diffs} => (name, diffs, s! "lib_apply {pathPosToPos path pos} {name} {goalPos}")
  -- return resultStrings



elab "try_lib_apply" goalPos:treePos : tactic => do
  let goalPos := getPosition goalPos
  let tree := (← getMainDecl).type
  logLibrarySearch (← librarySearchApply' goalPos tree)

-- #exit
example : ∃ x, x = 4 := by
  make_tree
  try_lib_apply [1]

-- #print prefix Aesop.Check.script
#check Aesop.Check.script.sizeOf_spec
#check Aesop.Check.all.sizeOf_spec

#check Nat.Coprime

#exit
example (hf : (mulSupport f).Finite) (hg : (mulSupport g).Finite) : 
  ( ∏ᶠ i, f i * g i )= (∏ᶠ i, (f i + 1)) * (∏ᶠ i : α, g i) := by
    try_lib_rewrite [0,1]
