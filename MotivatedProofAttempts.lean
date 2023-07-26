import Implementations
import Skolem
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.NormNum
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Separation
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

lemma InversePlusTwo : ∃ g : ℤ → ℤ, g ∘ (fun x ↦ x + 2) = id := by
  refine ⟨?g, ?_⟩
  on_goal 2 =>
    ext x; dsimp
    set y := x + 2
    -- Why (programatically) would we seek to write `x` wrt `y`?
    have' hx : x = y - 2 := by norm_num
    -- should have point-and-click support via `conv` (soon)
    sorry
    -- rewriteAt [2] [hx]
  -- now instantiate the metavariable of `g` based on the current proof state
  on_goal 1 => 
    exact fun y => y - 2
  
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
    have hF₁Comp : IsCompact F₁ := sorry
    have hF₂Comp : IsCompact F₂ := by exact IsClosed.isCompact hF₂
  all_goals { sorry }
-- `∀ y, y ∈ S ↔ y ∉ f y`
-- instantiate y with `x`, match with `hs : f x = S`
-- obtain `x ∈ S ↔ x ∉ S`, contradiction

open Function

lemma temp {P : Prop} : P → ¬ P → False := fun y x => x y

lemma Cantor (f : α → Set α) : ¬ Surjective f := by
  intro h
  rw [Surjective] at h
  replace h : ¬ ∃ (S : Set α), ∀ (i : α), ∃ (j : α), ¬ (j ∈ f i ↔ j ∈ S) := by
    push_neg
    convert h
    rw [Set.ext_iff]
  -- negateHypothesis move we still need to adjust
  apply temp h
  clear h
  skolemize_goal
  simp only [not_exists, not_forall, not_not]
  refine ⟨?S, ?j, fun i => ?_⟩
  on_goal 3 =>
    set P := fun x => ?j x ∈ f x with hP
    suffices ¬ (P i ↔ ?j i ∈ ?S) by { convert this }
    rw [not_iff]
    constructor
    on_goal 1 => 
      intro hnP
      rw [← Set.mem_setOf (a := i) (p := P)] at hnP
      -- the following `move` takes a bit long in Lean but we should translate it to be more mechanical
      replace hnP : i ∈ {x | ¬ P x} := by
        simp
        rw [Set.mem_setOf] at hnP
        exact hnP
      replace hnP : ?j i ∈ ?j '' {x | ¬ P x} := by exact Set.mem_image_of_mem ?j hnP
      apply Set.mem_of_mem_of_subset hnP
      on_goal 3 =>
        refine ?j '' {x | ¬ (fun x => ?j x ∈ f x) x}
      -- Freddy instantiates `?S` with `?j '' {x | ¬ P x}` here but currently metavariables
      -- do not appear as variables in each others' contexts
      -- `TODO: Fix this behaviour` 
      rfl
    on_goal 4 =>
      contrapose
      on_goal 2 =>
        rw [not_not]
        intro hPi
        intro hi 
        simp at hi
        obtain ⟨k, ⟨hkf, hki⟩⟩ := hi
        negateHypothesis hkf
        convert hPi
        -- now instantiate a `?j` with the identity
        on_goal 2 => 
          exact id
        exact hki