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
