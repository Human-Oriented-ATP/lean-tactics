import Skolem
import Mathlib.Data.Nat.Order.Basic

-- basic skolemization tests
example : ∀ x : Nat, ∃ y : Nat, y > x := by
  skolemize_goal
  exists (λ x => x + 1)
  simp

example (f : Nat → Nat) (hf : ∀ x : Nat , ∃ y : Nat, f y > x) :
  ∃ g : Nat → Nat, ∀ x : Nat, (f ∘ g) x > x := by
  skolemize_hypothesis hf
  exact hf

--advanced skolemization tests
example : ∀ x : Nat, ∀ y : Nat, ∃ z : Nat, z > x + y := by
  skolemize_all
  exists (λ x y => x + y + 1)
  simp

example {p : Prop} (hP : p) (f : Nat → Nat)
  (h' : p → p ∧ (∀ x : Nat , ∃ y : Nat, f y > x)) :
  ∃ g : Nat → Nat, ∀ x : Nat, (f ∘ g) x > x := by
  skolemize_everything
  exact (h' hP).right
