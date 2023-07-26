
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Function
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import RewriteOrd


def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε


theorem coincide {x y : ℝ}: (∀ {ε : ℝ}, ε > 0 → |x - y| < ε) → x = y := by
  intro h
  by_contra neq
  have this : |x - y| > 0 := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro h''
    apply neq
    apply eq_of_abs_sub_eq_zero h''.symm
  have : |x - y| / 2 > 0 := by linarith
  have : |x - y| < |x - y| / 2 := by exact h this
  linarith


theorem lim_unique {s : ℕ → ℝ} {a b : ℝ} (sa : ConvergesTo s a) (sb : ConvergesTo s b) : a = b := by
  apply coincide -- Using `library_search`, we set the subtask of showing that ∀ ε : |a - b| < ε.
  intro ε εpos
  have : ε / 2 > 0 := by linarith -- Not sure about how to motivate this.
  rcases sa (ε / 2) this with ⟨Na, hNa⟩ -- Expand definition.
  rcases sb (ε / 2) this with ⟨Nb, hNb⟩

  -- Unsure about how to motivate this.
  let N := max Na Nb

  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by congr; ring
    _ ≤ |(-(s N - a))| + |s N - b| := (abs_add _ _)
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε / 2 + ε / 2 := by
      have absa : |s N - a| < ε / 2 := by
        apply hNa
        apply le_max_left
      have absb : |s N - b| < ε / 2:= by
        apply hNb
        apply le_max_right
      apply add_lt_add absa absb
    _ = ε := by norm_num


theorem lim_unique_motivated {s : ℕ → ℝ} {a b : ℝ} (sa : ConvergesTo s a) (sb : ConvergesTo s b) : 
  a = b := by
  apply coincide -- Using `library_search`, we set the subtask of showing that `∀ ε > 0, |a - b| < ε`
  contrapose! sa
  obtain ⟨ε, hεpos, hε⟩ := sa
  rw [ConvergesTo]
  push_neg
  refine ⟨?δ, ?_, ?_⟩
  on_goal 3 =>
    intro N
    -- the following step is `not` motivated and only done here because of the 
    -- issue with metavariables discussed previously
    specialize sb (ε - ?δ) _
    on_goal 3 =>
      cases' sb with M hM
      refine ⟨?n, ?_, ?_⟩
      on_goal 4 =>
        specialize hM ?n _
        on_goal 3 =>
          -- version of triangle inequality
          have : |a - b| - |s ?n - b| ≤ |s ?n - a| := by sorry
          rewriteOrdAt [1] [← this]
          rewriteOrdAt [1, 0, 1] [← hε]
          rewriteOrdAt [1, 1] [le_of_lt hM]
          norm_num
  -- inspecting the goal states we have the conditions `?n ≥ N` and `?n ≥ M`
  case n =>
    exact max M N
  -- inspecting the goal states we have the conditio `0 < ?δ` and `0 < ε - ?δ`
  case δ =>
    exact (ε / 2)
  . exact half_pos hεpos -- found by `exact?`
  . { norm_num; exact hεpos } -- 2nd part found by `exact?`
  . exact Nat.le_max_right M N -- found by `exact?`
  . exact Nat.le_max_left M N -- found by `exact?`


namespace Function

-- One way of doing it in Lean.
theorem Cantor1 : ∀ f : α → Set α, ¬Surjective f := by
  intro f -- Happens automatically.
  by_contra surjf
  let S := { x | x ∉ f x } -- This can be motivated, I think.
  /-
  There are many different kinds of definitions. I'd advocate having moves which allows the user
  to unfold the definition piecemeal, e.g. one move corresponding to `specialize` and another to `rcases`.
  -/
  -- specialize surjf S -- Expand definition.
  rcases surjf S with ⟨x, hs⟩ -- Expand definition.
  observe : x ∈ S ↔ x ∈ f x -- Expand definition. However, this might be tricky to implement, since the user must type the lemma.
  simpa -- Basic rewriting.

-- An attempt at a motivated proof.
theorem Cantor_motivated : ∀ (f : α → Set α), ¬Surjective f := by
  intro f
  by_contra surjf
  dsimp [Surjective] at surjf
  contrapose! surjf
  refine ⟨?S, ?_⟩
  on_goal 2 =>
    intro x eq
    rw [Set.ext_iff] at eq
    revert eq
    rw [imp_false]
    push_neg
    use x
  case S =>
    exact { x | x ∉ f x }
  on_goal 1 =>
    simp
    exact em (x ∈ f x)

end Function

section Function

open NNReal
-- https://www.codewars.com/kata/5ea281b8888eba001fd3d77c

variable [MetricSpace α][MetricSpace β]
variable {K : ℝ≥0} {f : α → β}

example (hk : K > 0) : ∀ {f : α → β}, LipschitzWith K f → UniformContinuous f := by
  intro f l
  rw [lipschitzWith_iff_dist_le_mul] at l
  rw [Metric.uniformContinuous_iff]
  intro ε εpos
  refine ⟨?d₁, ?_⟩
  on_goal 2 =>
    refine ⟨?d₂, ?_⟩
    on_goal 3 =>
      intro x y hd₁
      suffices : ↑K * dist x y < ε
      specialize l x y
      apply lt_of_le_of_lt l this
    case d₁ =>
      exact ε / K
    sorry
  sorry

end Function

open Set Topology Filter

variable {X Y : Type _} [MetricSpace X] [MetricSpace Y] {f : X → Y}

theorem TendstoUniformly'.continuous (h₂ : TendstoUniformly F f p)
    (h₁ : ∀ᶠ n in p, Continuous (F n)) [NeBot p] : Continuous f := by
  rw [Metric.continuous_iff] -- expand(π, T)
  intro x ε εpos
  refine ⟨?d₁, ?_⟩
  on_goal 2 =>
    refine ⟨?d₂, ?_⟩
    on_goal 3 =>
      intro y hd₁ -- targetImplicationSplit(π, T)
      rw [tendstoUniformly_iff_tendsto] at h₂ -- expand(π h₂)
      -- Arriving at the standard ε δ-definition requires a great deal of work, since Mathlib only stores the most general results.
      sorry
    sorry
  sorry


namespace Function

variable {X Y : Type _} [MetricSpace X] [MetricSpace Y] {f : X → Y}

theorem UniformContinuous_of_continuous : UniformContinuous f → Continuous f := by
  intro h₁ 
  rw [Metric.uniformContinuous_iff] at h₁
  rw [Metric.continuous_iff] 
  intro x ε εpos
  specialize h₁ ε
  simp [εpos] at h₁
  -- aesop
  rcases h₁ with ⟨δ, hd⟩
  use δ
  constructor
  . exact hd.left
  . intro a h
    apply hd.2 h


theorem UniformContinuous_of_continuous_motivated : UniformContinuous f → Continuous f := by
  intro h -- Preprocessing.
  rw [Metric.uniformContinuous_iff] at h -- Expand definition.
  rw [Metric.continuous_iff] -- Expand definition.
  intro x ε εpos -- Preprocessing.
  specialize h ε -- Peel quantifier/skolemization.
  simp [εpos] at h -- Basic rewriting.
  rcases h with ⟨δ, ⟨h₁, h₂⟩⟩ -- Basic rewriting/naming.
  use δ -- Hard to motivate this.
  exact ⟨h₁, λ a ↦ h₂⟩ 

end Function

open Group

variable {G : Type _} [Group G]
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Subgroup/Basic.html#Subgroup.normal_subgroupOf_iff

theorem Trivial_normal_motivated {G : Type _} [Group G] : Subgroup.Normal (⊥ : Subgroup G) := by
  refine { conj_mem := ?_ } -- Expand definition.
  intro n hn g  -- Intro.
  -- You can do aesop from here.
  rw [hn] -- Basic rewriting/naming.
  rw [mul_one, mul_inv_self g] -- Basic rewriting.
  trivial

theorem testy {G : Type _}  [inst : Group G]  {M : Type _}  [inst : MulOneClass M]  (f : G →* M) : Subgroup.Normal (MonoidHom.ker f) := by
  refine { conj_mem := ?_ } -- Expand definition.
  intro n hn g -- Skolemize.
  rw [MonoidHom.mem_ker]
  rw [MonoidHom.mem_ker] at hn
  simp
  rw [hn, mul_one]
  rw [← @MonoidHom.map_mul, mul_inv_self g]
  exact MonoidHom.map_one f

theorem testy1 {G : Type _}  [inst : Group G]  {M : Type _}  [inst : MulOneClass M]  (f : G →* M) : Subgroup.Normal (MonoidHom.ker f) := by
  refine { conj_mem := ?_ }
  intro n hn g
  rw [MonoidHom.mem_ker, @MonoidHom.map_mul, @MonoidHom.map_mul, hn, mul_one, ← @MonoidHom.map_mul, mul_inv_self g]
  exact MonoidHom.map_one f

theorem testy2 {G : Type _} [inst : Group G]  {M : Type _}  [inst : MulOneClass M]  (f : G →* M) : Subgroup.Normal (MonoidHom.ker f) := by
  refine { conj_mem := ?_ }
  intro n hn g
  rw [MonoidHom.mem_ker]
  sorry

theorem abelian' {G : Type _} [Group G] (h : ∀ (x : G), x ≠ 1 → orderOf x = 2) : ∀ (a b : G), Commute a b := by
  intro a b
  rw [Commute, SemiconjBy]
  have h' : ∀ (x : G), x ^ 2 = 1 := by
    intro x
    by_cases hi : x = 1
    . rw [hi]
      exact one_pow 2
    . specialize h x
      refine Iff.mp orderOf_dvd_iff_pow_eq_one ?_
      have : orderOf x = 2 := h hi
      rw [this]
  have h'' : ∀ (x : G), x⁻¹ = x := by
    intro x
    rw [@inv_eq_iff_mul_eq_one, ← pow_two, h']
  have : a * b = b * a ↔ a * b * (a⁻¹ * b⁻¹) = 1 := by
    constructor
    . rw [h'', h'', ← pow_two, h']
      intro h
      trivial
    . intro h
      rw [← mul_assoc] at h
      exact Iff.mp commutatorElement_eq_one_iff_mul_comm h
  rw [this, h'', h'']
  exact Iff.mp inv_eq_iff_mul_eq_one (h'' (a * b))


theorem abelian2 {G : Type _} [Group G] (h : ∀ (x : G), x ≠ 1 → orderOf x = 2) : ∀ (a b : G), Commute a b := by
  intro a b
  rw [Commute, SemiconjBy]
  rw [← @inv_mul_eq_iff_eq_mul, ← @mul_assoc]
  have h' : ∀ (x : G), x ^ 2 = 1 := by
    intro x
    by_cases hi : x = 1
    . rw [hi]
      exact one_pow 2
    . specialize h x
      refine Iff.mp orderOf_dvd_iff_pow_eq_one ?_
      have : orderOf x = 2 := h hi
      rw [this]
  have h'' : ∀ (x : G), x⁻¹ = x := by
    intro x
    rw [@inv_eq_iff_mul_eq_one, ← pow_two, h']
  have : b⁻¹ * (a * b) = a ↔ a⁻¹ * b⁻¹ * (a * b) = 1 := by
    constructor
    . intro hh
      rw [@mul_assoc]
      rw [← mul_assoc, h'', h'', ← pow_two, h']
    . sorry
  sorry