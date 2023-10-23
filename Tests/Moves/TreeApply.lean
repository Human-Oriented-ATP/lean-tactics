import MotivatedMoves.Moves.TreeApply

example (p q : Prop) : ((p → q) ∧ p) → (q → False) → False := by
  make_tree
  tree_apply [0,0,1] [1,0,0]
  tree_apply' [0] [1,0,0]
  tree_apply [1,0] [1,1]

example : ({α : Type 0} → {r : α → α → Prop} → [IsRefl α r] → (a : α) → r a a) → 3 = 3 := by
  make_tree
  tree_apply [0,1,1,1,1] [1]

lemma cantor_end : ∀ (X : Type u) (f : X → Set X), ∃ a : Set X, ∀ a_1 : X,
¬a_1 ∈ f a_1 ↔ a_1 ∈ a := by
  make_tree
  lib_apply [1,1,1,1] refl [1, 1, 1, 1, 2]

example (p : Prop) : (∀ _n:Nat, p) → p := by
  make_tree
  tree_apply [0,1] [1]

example (p : Nat → Prop): (∀ m, (1=1 → p m)) → ∀ m:Nat, p m := by
  make_tree
  tree_apply [0,1,1] [1,1]
  rfl

example (p q : Prop) : p → (p → q) → q := by
  make_tree
  tree_apply [0] [1,0,0]
  -- q → q
  tree_apply [0] [1]

example (p q : Prop) : p → (p → q) → q := by
  make_tree
  tree_apply [1,0,1] [1,1]
  -- p → p
  tree_apply [0] [1]
  
example (p q : Prop) : p → (p → q) → q := by
  make_tree
  tree_apply [1,0,0] [0]
  -- p → p
  tree_apply [0] [1]

example (p q r : Prop) : (q → p) → (q ∧ r) → p := by
  make_tree
  tree_apply [1,0,0] [0,0]
  tree_apply [0] [1,1]

example (p q : Prop) : p ∧ (p → q) → q := by
  make_tree
  tree_apply [0,0] [0,1,0]
  -- q → q
  tree_apply [0] [1]
  
example (p q : Prop) : ((p → q) ∧ p) ∧ p → q := by
  make_tree
  tree_apply [0,1] [0,0,0,0]
  -- q → q
  tree_apply [0,0] [1]

example (p q : Prop) : (p → q) → p → q := by
  make_tree
  tree_apply [1,0] [0,0]
  -- q → q
  tree_apply [0] [1]
  
example (p q : Prop) : ((q → p) → p → q) → True := by
  make_tree
  tree_apply [0,1,0] [0,0,1]
  lib_apply trivial [1]

example (p q r s: Prop) : (p → q → r → s) → q → True := by
  make_tree
  tree_apply [0,1,0] [1,0]
  -- q → q
  lib_apply trivial [1]

example (p : Prop) : p → p := by
  make_tree
  tree_apply [0] [1]

example [Preorder α] (a b : α) : a < b → a ≤ b := by
  make_tree
  lib_apply le_of_lt [0]
  tree_apply [0] [1]
  
example [Preorder α] (a b : α) : a < b → a ≤ b := by
  make_tree
  lib_apply [1,1,1,1,1] le_of_lt [1]
  tree_apply [0] [1]
  
example [Preorder α] (a b : α) : a < b → a ≤ b := by
  make_tree
  lib_intro le_of_lt
  tree_apply [0,1,1,1,1] [1]

example : p → ¬ p → q := by
  make_tree
  tree_apply [1,0,1] [0]

example : ¬ p → p → q := by
  make_tree
  tree_apply [1,0] [0,1]

example : p → ¬ p → q := by
  make_tree
  tree_apply [0] [1,0,1]

example : ¬ p → p → q := by
  make_tree
  tree_apply [0,1] [1,0]

example : (p → False) → ¬ p := by
  make_tree
  tree_apply [0,0] [1,1]
  simp