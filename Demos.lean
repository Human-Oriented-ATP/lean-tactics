import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem coincide (x y : ℝ): (∀ {ε : ℝ}, ε > 0 → |x - y| < ε) → x = y := by
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

  -- Two lemmas needed for the calculation.
  let N := max Na Nb
  have absa : |s N - a| < ε / 2 := by 
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε / 2:= by
    apply hNb
    apply le_max_right

  -- Unsure about how to motivate this.
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by congr; ring
    _ ≤ |(-(s N - a))| + |s N - b| := (abs_add _ _)
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε / 2 + ε / 2 := (add_lt_add absa absb)
    _ = ε := by norm_num

end

namespace function

def Surj (f : α → β) : Prop := ∀ b, ∃ a, f a = b
macro "expand" d:ident x:ident y:ident h:ident : tactic => `(tactic| rcases $d:ident $x:ident with ⟨$y:ident, $h:ident⟩)

-- One way of doing it in Lean.
theorem Cantor1 : ∀ f : α → Set α, ¬Surj f := by
  intro f
  by_contra surjf
  let S := { x | x ∉ f x }
  rcases surjf S with ⟨x, hs⟩ 
  have : x ∈ S ↔ x ∈ f x := by rw [hs]
  simpa -- simp [Set.mem_setOf] at this 

-- An attempt at a motivated proof.
theorem Cantor2 : ∀ f : α → Set α, ¬Surj f := by
  intro f -- Happens automatically.
  by_contra surjf
  let S := { x | x ∉ f x }  -- This can be motivated, I think.
  /-
  There are many different kinds of definitions. I'd advocate having moves which allows the user 
  to unfold the definition piecemeal, e.g. one move corresponding to `specialize` and another to `rcases`. 
  -/
  specialize surjf S -- Expand definition.
  rcases surjf with ⟨x, hs⟩ -- Expand definition.
  have : x ∈ S ↔ x ∈ f x := by rw [hs] -- Expand definition. However, this might be tricky to implement, since the user must type the lemma.
  simpa -- Basic rewriting.

-- Another attempt at motivated proof.
theorem Cantor3 : ∀ f : α → Set α, ¬Surj f := by
  intro f
  by_contra surjf
  let S := { x | x ∉ f x }
  have : ∀ x, x ∈ S ↔ x ∉ f x := by simp [Set.mem_setOf] -- Expand definition.
  expand surjf S x hs -- Expand definition.
  exact false_of_a_eq_not_a (congrFun hs x) 