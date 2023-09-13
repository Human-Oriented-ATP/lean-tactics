import Mathlib
import Implementations




-- Rewriting

example : ∀ n, n + 1 + 1 = n + 2 := by
  rewriteAt [1,0,1] [Nat.add_assoc]
  intro n
  rfl


example : ∀ (m : ℕ) n, (n = 1 ∧ True) = (1 = n ∧ True) := by
  rewriteAt [1, 1, 0, 1, 0, 1] [eq_comm]
  intro _ _
  rfl

lemma symm_iff (a b : α) : a = b ↔ b = a := eq_comm

example (α : Nat → Type u) (h : ∀ (n : Nat) (_ : α n), (n = 1 ∧ True) = (1 = n ∧ True)) : True := by
  have this := symm_iff (α := ℕ)
  specialize this ?x ?y
  rewriteAt [1, 1, 0, 1, 0, 1] [this] at h
  on_goal 3 => trivial
  exact 24236
  exact 5432



example {p q : ℕ  → ℕ → Prop} {α : ℝ → Type u} (h₁ : a = b) (h₂ : ∀ q, q = p) : ∀ z : ℝ, ∀ _ : α z, (q b a → p a b) ∧ z = z := by
  rewriteAt  [1,1,0,1,1,0,1] [h₁]
  rewriteAt [1,1,0,1,0,1] [h₁]
  rewriteAt [1,1,0,1,0,0,0] [h₂]
  exact λ _ _ ↦ ⟨id, rfl⟩

  
example : 0 = (0: ℝ)  ∧ 0 = 1-(1 : ℤ) ∧ 0 = 1-(1 : ℤ)  := by
refine ⟨ l•, r•⟩ 
on_goal 1 =>
  rewriteAt [0,1] [← sub_self]
  rewriteAt [1] [← sub_self]
on_goal 5 =>
  constructor
  on_goal 2 => rewriteAt [0,1] [← sub_self (G := ℤ )]
  on_goal 1 => rewriteAt [0,1] [← sub_self (G := ℤ )]
  rfl
  rfl
rfl
exact 100

--try the tactic-out below 
example : 0 = (0: ℝ)  ∧ 0 = 1-(1 : ℤ) ∧ 0 = 1-(1 : ℤ) := by sorry



-- RewriteOrd

example [Preorder α] {a b c : α} (h : b ≤ a) (g : c ≤ b) : (True → a ≤ c) → True := by
  rewriteOrdAt [0,1,0,1] [← h]
  rewriteOrdAt [0,1,1] [g]
  intro _
  trivial


-- set_option pp.explicit true
variable {α : Type u} (a : α) [Preorder α]


example {P Q : α → Prop} (h : ∀ a, P a → Q a) ( g : ∀ a, P a) : (a:α) → Q a := by
rewriteOrdAt [1] [← h]
exact g




example {A B : Set α} (h : ∀ B, A ⊆ B) (g : a ∈ A) : ∀ b : Set α, a ∈ b := by
rewriteOrdAt [1,1] [← h]
exact fun _ => g