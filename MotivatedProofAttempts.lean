import Implementations
import Skolem
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.NormNum
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Separation

lemma InversePlusTwo : ∃ g : ℤ → ℤ, g ∘ (fun x ↦ x + 2) = id := by
  refine ⟨?g, ?_⟩
  on_goal 2 =>
    ext x; dsimp
    set y := x + 2
    -- Why (programatically) would we seek to write `x` wrt `y`?
    have' hx : x = y - 2 := by norm_num
    -- should have point-and-click support via `conv` (soon)
    rewriteAt [2] hx
  -- now instantiate the metavariable of `g` based on the current proof state
  on_goal 1 => 
    exact fun y => y - 2
  rfl

lemma GroupTheoryES1Q1 {G : Type u} [Group G] : ∀ (g : G), (g * g = g → g = 1) := by 
  intro g hg
  -- `library_search` should find the lemma `self_eq_mul_left/right`
  -- `Update` : have since decided that use of this result would be considered cheating
  rw [← self_eq_mul_left]
  -- Want to match the current hypothesis `hg` with the goal that has a metavariable
  -- Only thing in the way is that the expression matches `Eq.Symm hg` instead of `hg` itself.
  -- Seems like we'll need special support for this
  convert Eq.symm hg

-- I feel like this should be harder
/-- Let `X` be a `compact Hausdorff` space and let `F₁, F₂ ⊂ X` be `closed and disjoint`. Show
that there are `disjoint open` subsets `G₁, G₂ ⊂ X` with `F₁ ⊂ G₁` and `F₂ ⊂ G₂` -/
lemma AnalysisTopologyES3Q7 {X : Type u} [TopologicalSpace X] [CompactSpace X] [hT₂: T2Space X] 
  (F₁ F₂ : Set X) (hF₁ : IsClosed F₁) (hF₂ : IsClosed F₂) (hdisj: Disjoint F₁ F₂) :
  ∃ G₁ G₂ : Set X, F₁ ⊂ G₁ ∧ F₂ ⊂ G₂ ∧ Disjoint G₁ G₂ ∧ IsOpen G₁ ∧ IsOpen G₂:= by
  refine ⟨?G₁, ?G₂, ?_⟩
  on_goal 3 =>
    have hHaus := hT₂.t2
    -- have to extract the finite subcover definition of compactness
    have hF₁Comp := sorry

    
    have hF₂Comp : IsCompact F₂ := by exact IsClosed.isCompact hF₂



