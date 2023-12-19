import MotivatedMoves.GUI.MotivatedProofList

lemma simple_inverse : ∃ f : ℤ → ℤ, ∀ n, f (n+1) = n := by
motivated_proof
tree_name m [1, 1, 2, 0, 1, 1]
lib_rewrite_rev eq_sub_iff_add_eq [1, 1, 1, 0, 2]
tree_rewrite [1, 1, 1, 0, 2, 0, 1] [1, 1, 1, 1, 2, 1]
lib_apply refl [1, 1, 2]


example : (α : Type u) → [MetricSpace α] → [CompleteSpace α] → ∀ n, CompleteSpace (Fin n → α) := by
motivated_proof
lib_rewrite [1, 1, 2, 0, 1] completeSpace_iff_ultrafilter [1, 1, 1, 1, 2]
lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] cauchy_pi_iff' [1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 2, 0, 1] completeSpace_iff_ultrafilter [1, 1, 0, 2]
lib_rewrite [1, 1, 1, 1, 2, 1] Ultrafilter.coe_map [1, 1, 1, 1, 1, 0, 1, 2, 1]
tree_apply [1, 1, 0, 1, 0, 2] [1, 1, 1, 1, 1, 0, 1, 2]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] nhds_pi [1, 1, 1, 1, 1, 1, 2, 1]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] Filter.le_pi [1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] Ultrafilter.coe_map [1, 1, 1, 1, 0, 1, 1, 2, 0, 1]
lib_rewrite [1, 1, 1, 1, 1, 1, 2, 0, 1] tendsto_nhds [1, 1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] le_nhds_iff [1, 1, 1, 1, 0, 1, 1, 2]
lib_rewrite [1, 1, 1, 2, 0, 1] Classical.skolem [1, 1, 1, 1, 0]
tree_apply [1, 1, 1, 1, 0, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
tree_apply [1, 1, 1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 2]
lib_rewrite [1, 1, 1, 1, 1, 2, 1] Filter.mem_map [1, 1, 1, 1, 1, 1, 1, 2]
tree_apply [1, 1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 2]



example : (α β : Type) → [PseudoMetricSpace α] →  [PseudoMetricSpace β] → (f : α → β) → (F : ℕ → α → β) →
  (∀ n, Continuous (F n)) → TendstoUniformly F f Filter.atTop → Continuous f := by
motivated_proof
lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] Metric.continuous_iff [1, 1, 1, 1, 1, 1, 0, 1, 2]
lib_rewrite [1, 1, 1, 1, 1, 1, 1, 2, 0, 1] Metric.tendstoUniformly_iff [1, 1, 1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] Metric.continuous_iff [1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] Filter.eventually_atTop [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 2]
lib_rewrite_ord [1, 1, 1, 1, 1] dist_triangle [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
tree_rewrite_ord' [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 0, 1]
lib_rewrite_ord [1, 1, 1, 1, 1] dist_triangle [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] dist_comm [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1]
tree_rewrite_ord [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1]
tree_rewrite_ord [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 0, 1]
tree_apply [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
sorry

lemma Infinitude_of_Primes : ∀ n : ℕ, ∃ p : ℕ, n ≤ p ∧ Nat.Prime p := by 
motivated_proof
lib_apply * [1, 1, 1, 0] Nat.exists_prime_and_dvd [1, 1, 1, 2]
tree_contrapose [1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 1, 2, 1] Nat.not_dvd_iff_between_consec_multiples [1, 1, 1, 1, 1, 1, 2]
tree_name pk [1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 0, 1]
lib_rewrite [1, 1, 2, 1] Nat.succ_le_iff [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
lib_apply  [1, 1, 1] Nat.le_of_eq [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2] 
lib_apply * [1] Nat.succ_succ_ne_one [1, 1, 0, 2]
lib_rewrite [1, 1, 2, 0, 1] Nat.succ_inj' [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
tree_rewrite [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 0, 1]
tree_rewrite' [1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
lib_rewrite [1, 2, 1] Nat.add_one [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
lib_rewrite [1, 1, 1, 1, 1, 1, 2, 0, 1] mul_add_one [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1]
lib_rewrite [1, 1, 1, 2, 0, 1] Nat.add_lt_add_iff_left [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_apply * [1, 1] Nat.Prime.one_lt [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
tree_apply' [1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 2, 0, 1] Nat.mul_div_eq_iff_dvd [1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_apply * [1, 1] Nat.Prime.pos [1, 1, 1, 1, 1, 1, 0, 2]
tree_apply [1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 0, 2]
tree_induction []
tree_simp [0, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 2, 0, 1] Nat.lt_add_one_iff [1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 2, 1] Nat.not_lt [1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] not_lt_iff_eq_or_lt [1, 1, 1, 1, 1, 0, 2]
tree_induction [1, 1, 1, 1, 1]
tree_rewrite [1, 1, 1, 1, 1, 0, 0, 2, 1] [1, 1, 1, 1, 1, 0, 1, 2, 0, 1]
tree_simp [1, 0, 1, 0, 2]
tree_rewrite_ord [1, 0, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
tree_apply [1, 1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 0, 2]
tree_simp []
lib_rewrite [1, 1, 1, 1, 1, 1, 2, 1] lcm_dvd_iff [1, 1, 1]
tree_name m [1, 1, 1, 2, 1]
lib_apply * [1, 1, 1, 1, 1] Eq.dvd [1, 1, 1, 1, 1, 2]
tree_rewrite [1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 1, 2, 1]
lib_rewrite [1, 1, 1, 1, 2, 1] Nat.sub_eq_iff_eq_add [1, 1, 1, 2]
lib_apply refl [1, 1, 1, 1, 2]
lib_rewrite [1, 2, 0, 1] Nat.one_le_iff_ne_zero [1, 1, 2]
tree_simp []
-- `¬n = 0`
sorry


lemma Infinitude_of_PrimesPos : ∀ n > 0, ∃ p : ℕ, n ≤ p ∧ Nat.Prime p := by
motivated_proof
try_lib_apply []
lib_apply * [1, 1, 1, 0] Nat.exists_prime_and_dvd [1, 1, 1, 1, 2]
tree_contrapose [1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 1, 2, 1] Nat.not_dvd_iff_between_consec_multiples [1, 1, 1, 1, 1, 1, 1, 2]
tree_name m [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 0, 1]
lib_rewrite [1, 1, 2, 1] Nat.succ_le_iff [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
lib_apply * [1, 1, 1] Nat.le_of_eq [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
lib_apply * [1] Nat.succ_succ_ne_one [1, 1, 1, 0, 2]
lib_rewrite [1, 1, 2, 0, 1] Nat.succ_inj' [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
tree_rewrite [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 0, 1]
tree_rewrite' [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
lib_rewrite [1, 1, 1, 1, 1, 1, 2, 0, 1] mul_add_one [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1]
lib_rewrite [1, 2, 1] Nat.add_one [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
lib_rewrite [1, 1, 1, 2, 0, 1] Nat.add_lt_add_iff_left [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_apply * [1, 1] Nat.Prime.one_lt [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
tree_apply' [1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 2, 0, 1] Nat.mul_div_eq_iff_dvd [1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_apply * [1, 1] Nat.Prime.pos [1, 1, 1, 1, 1, 1, 1, 0, 2]
tree_apply [1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 0, 2]
tree_induction []
tree_simp [0, 0, 2]
lib_rewrite [1, 1, 2, 0, 1] Nat.lt_add_one_iff [1, 1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 2, 1] Nat.not_lt [1, 1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] not_lt_iff_eq_or_lt [1, 1, 1, 1, 1, 1, 0, 2]
tree_induction [1, 1, 1, 1, 1, 1]
tree_rewrite [1, 1, 1, 1, 1, 1, 0, 0, 2, 1] [1, 1, 1, 1, 1, 1, 0, 1, 2, 0, 1]
sorry



example : {f g : ℝ → ℂ} → {x : ℝ} → {a b : ℂ} → (hf : HasDerivAt f a x) → (hg : HasDerivAt g b x) → 
    HasDerivAt (fun x => f x + g x) (a + b) x := by
  motivated_proof
  try_lib_apply [1,1,1,1,1,1,1]



example : [PseudoMetricSpace α] → [PseudoMetricSpace β] → (f : α → β)
  → UniformContinuous f → Continuous f := by
  make_tree
  lib_rewrite Metric.uniformContinuous_iff [1,1,1,0]
  lib_rewrite Metric.continuous_iff [1,1,1,1]
  tree_apply [1,1,1,0,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,1,0] [1,1,1,1,0]
  tree_apply [1,1,1,0] [1,1,1,1,1,0]
  tree_search

example [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) : 
  LipschitzWith 1 f → Continuous f := by
  make_tree
  lib_rewrite Metric.continuous_iff [1]
  lib_rewrite lipschitzWith_iff_dist_le_mul [0]
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

-- See here the lack of ability to case split :((
lemma imp_exists [Nonempty α] {q : α → Prop} {p : Prop} : (∃ a : α, p → q a) ↔ p → ∃ a : α, q a := by
revert α p
motivated_proof
lib_rewrite [1, 1, 2, 0, 1] iff_def [1, 1, 1, 1, 2]
tree_apply [1, 1, 1, 1, 0, 0, 1, 1, 2] [1, 1, 1, 1, 0, 1, 1, 1, 2]
tree_apply [1, 1, 1, 1, 0, 0, 2] [1, 1, 1, 1, 0, 1, 2]
lib_rewrite [1, 1, 1, 2, 0, 1] Classical.skolem [1, 1, 1, 1, 0]
tree_induction [1, 1, 1, 1]
sorry
example : ∀ (α : Type u) (p : Prop) (q : α → Prop) (a : α), (p → ∃ b : α, q b) → ∃ b : α, p → q b := by
make_tree
sorry



example : ∀ (α β : Type*), [PseudoMetricSpace α] → [PseudoMetricSpace β] → (f : α → β) → (F : ℕ → α → β) →  
  (∀ n, Continuous (F n)) → TendstoUniformly F f Filter.atTop → Continuous f := by
motivated_proof
lib_rewrite [1,1,1,1,1,2,0,1] Metric.continuous_iff [1,1,1,1,1,1,0,1,2]
lib_rewrite [1,1,1,1,1,1,1,2,0,1] Metric.tendstoUniformly_iff [1,1,1,1,1,1,1,0,2]
lib_rewrite [1,1,1,1,2,0,1] Filter.eventually_atTop [1,1,1,1,1,1,1,0,1,1,2]
lib_rewrite [1,1,1,1,1,2,0,1] Metric.continuous_iff [1,1,1,1,1,1,1,1,2]
lib_rewrite [1,1,1,1,2,0,1] Tree.imp_exists_iff [1,1,1,1,1,1,1,0,1]
lib_rewrite [1,1,1,2,0,1] Classical.skolem [1,1,1,1,1,1,1,0]
tree_induction [1,1,1,1,1,1,1]
lib_rewrite_ord [1,1,1,1,1] dist_triangle [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1]
lib_rewrite_ord [1,1,1,1,1] dist_triangle [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1,0,1]
tree_rewrite_ord' [1,1,1,1,1,1,1,1,0,1,1,1,1,1,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1,0,1,0,1]
lib_rewrite [1,1,1,1,2,1] dist_comm [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1,1]
tree_rewrite_ord [1,1,1,1,1,1,1,1,0,1,1,1,1,1,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1,1]
tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2]
tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2]
tree_rewrite_ord [1,1,1,1,1,0,1,1,1,1,1,1,1,1,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1,0,1,1]
lib_apply refl [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2]
tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,0,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2]
tree_apply [1,1,1,1,1,1,0,2] [1,1,1,1,1,1,1,0,2]
lib_rewrite [1,1,1,1,1,2,0,1] add_right_comm [1,1,1,1,1,1,2,0,1]
lib_apply  [1,1,1,1,1,1,0] exists_add_lt_and_pos_of_lt [1,1,1,1,1,1,2]
tree_apply [1,1,1,1,1,0,2] [1,1,1,1,1,1,0,2]
tree_name xd [1,1,1,0,2,0,1,0,1]
tree_rewrite' [1,1,1,1,0,2] [1,1,1,1,1,0,2,0,1,1]
lib_rewrite [1,1,1,2,1] mul_two [1,1,1,1,1,0,2,0,1]
tree_rewrite [1,1,1,1,0,2,1] [1,1,1,1,1,0,2,0,1,0,1]
lib_rewrite [1,1,1,1,1,1,2,1] lt_div_iff [1,1,1,0,2]
tree_simp [1,1,1,0,0,2]
lib_rewrite [1,1,2,0,1] and_comm [1,1,1]
lib_rewrite [1,1,1,1,1,2,1] Set.mem_Ioo [1,1,1]
lib_rewrite [1,1,2,1] Set.nonempty_def [1,1]
lib_rewrite [1,1,1,1,1,2,0,1] Set.nonempty_Ioo [1,1,2]
lib_rewrite [1,1,1,1,1,1,2,0,1] lt_div_iff [1,1,2]
tree_simp [1, 1]
tree_apply [1, 0, 2] [1, 1, 2]





 
  
example (a b c : Int) : a + b + c = a + (b + c) := by
  try_lib_rewrite [2,0,1]

open BigOperators

example (N : ℕ) : ∑ n in Finset.range N, n  = N * (N - 1) / 2 := by
  try_lib_rewrite [2,0,1]

example (N : ℕ) : ∑ n in Finset.range N, (a + b)  = N * (N - 1) / 2 := by
  try_lib_rewrite [2,0,1]


-- See here the η-reduction awareness in action :))
example : Continuous Real.exp := by
motivated_proof
try_lib_apply []
lib_apply  [1, 1, 1, 1] Continuous.exp []
sorry

example : Continuous fun x => Real.exp x ^ 2 := by
motivated_proof
lib_apply  [1, 1, 1, 1, 1, 1] Continuous.rpow_const []
lib_apply  [] Real.continuous_exp [0, 2]
lib_apply  [1, 1, 1] Or.intro_right [1, 2]
lib_apply  [1, 1, 1, 1, 1] zero_le_two []
