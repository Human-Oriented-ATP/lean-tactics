
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Data.Set.Function
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus

namespace C03S06

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


theorem lim_unique2 {s : ℕ → ℝ} {a b : ℝ} (sa : ConvergesTo s a) (sb : ConvergesTo s b) : a = b := by
  apply coincide -- Using 'library_search', we set the subtask of showing that ∀ ε > 0, |a - b| < ε
  contrapose! sa
  obtain ⟨ε, hεpos, hε⟩ := sa
  rw [ConvergesTo]
  push_neg
  refine ⟨?δ, ?_, ?_⟩
  on_goal 3 =>
    intro N
    refine ⟨?n, ?_, ?_⟩
    on_goal 4 =>
      suffices : ?δ ≤ |a - b| - |s ?n - b|
  all_goals { sorry }

end C03S06

section

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
theorem Cantor2 : ∀ (f : α → Set α), ¬Surjective f := by
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
