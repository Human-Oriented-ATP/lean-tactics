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



#check HasDerivAt.add
example : {f g : ℝ → ℂ} → {x : ℝ} → {a b : ℂ} → (hf : HasDerivAt f a x) → (hg : HasDerivAt g b x) → 
    HasDerivAt (fun x => f x + g x) (a + b) x := by
  motivated_proof
  try_lib_apply [1,1,1,1,1,1,1]


-- #exit

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
-- convert

#eval show MetaM _ from do
  let n := ``HasDerivAt.add
  Mathlib.Tactic.LibrarySearch.processLemma n (← getConstInfo n)


open Lean Meta Elab Tactic
elab "hii" a:term : tactic => withReducible do
  let a ← elabTerm a none
  let r ← Tree.DiscrTree.reduceDT a {}
  logInfo r
  let r ← unfoldDefinition? a
  logInfo r

example (f g : Nat → Nat) : ∀ (α : Type) (S : Set α), S = ∅ := by
  make_tree
  try_lib_apply [1,1]
  hii  f+g
  sorry
variable (f g : Nat → Nat)
#check Lean.Meta.DiscrTree.reduceDT
#simp fun x => f x + g x
-- #check funext

example (p : (Nat → Int) → Prop) (f g : Nat → Int) (h : ∀ {f g}, p (f + g)) : p (fun x => 1 + 1) := by
  convert h
  

#exit  
  make_tree
  lib_rewrite Metric.tendstoUniformly_iff [1,0]
  try_lib_apply [1,0,1,1] -- this is the library search that hits a deterministic time-out
  lib_rewrite Filter.eventually_atTop [1,0,1,1]

  lib_rewrite Metric.continuous_iff [1,1]

  lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,2,0,1]
  tree_rewrite_ord' [1,0,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,2,0,1,0,1]
  lib_apply add_lt_of_lt_sub_left [1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  lib_rewrite_ord epsilon_lemma₁ [1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1]
  tree_search

  lib_rewrite_ord dist_triangle [1,1,1,1,1,1,1,1,1,1,1,1,2,0,1]
  lib_rewrite dist_comm [1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1,1]
  tree_rewrite_ord [1,0,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1,1]

  lib_apply add_lt_of_lt_sub_right [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  lib_rewrite_ord epsilon_lemma₁ [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1]
  tree_search
  lib_rewrite Metric.continuous_iff [0,1]
  tree_rewrite_ord [0,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,1]
  tree_apply [1,1,1,1,1,1,1,1,1,1,1,1,1,0] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0]
  tree_search
  lib_apply epsilon_lemma₂ [1,1,1,1,1,1,1,1,1]
  tree_search
  lib_rewrite_rev max_le_iff [1,1,1]
  lib_apply refl [1,1,1]




 
  
example (a b c : Int) : a + b + c = a + (b + c) := by
  try_lib_rewrite [2,0,1]

open BigOperators

example (N : ℕ) : ∑ n in Finset.range N, n  = N * (N - 1) / 2 := by
  try_lib_rewrite [2,0,1]

example (N : ℕ) : ∑ n in Finset.range N, (a + b)  = N * (N - 1) / 2 := by
  try_lib_rewrite [2,0,1]

/-

how to write a simplifier in a tree structure?

loop through the tree depth first.
At each node do the required pattern matches to do the simplifications
After the sub-branches have been searched, try to match again

relevant simplifications (in order of simplifying):
- pull out witnesses
- replace witness by regular hypothesis
- pushing negations?
- skolemize existentials & conjunctions in front of foralls & hypotheses
    when moving an existential in front of a hypothesis, try using the nonemptyness of the existential to get a general existential?
- deconstruct exitentials & conjunctions in hypotheses



what about skolemizing past conditions? Then the skolem function takes a proof as an argument. Oh but then the hypothesis has to become dependent :(.






```
s < α
∀ t, t < α ⇨ t ≤ β
⊢ s < β 

s < α
∀ t, t < α ⇨ t ≤ β
β ≤ s
⊢ False 

s < α
∀ t, t < α ⇨ t ≤ β
β ≤ s
β < α 
⊢ False 

∀ t, t < α ⇨ t ≤ β
β < α 
⊢ False 
```
`∀ t, t ∈ (β, α) ⇨ False`
`(β, α) = ∅`
`α ≤ β`



fun x => f x + g x = f + g
fun x => f x - g x = f - g
fun x => - f x = - f

Nat.add n m = n + m
Add.add n m = n + m

-/