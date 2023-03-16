-- sorry => tactic not implemented yet

-- basic skolemization tests
example : ∀ x : Nat, ∃ y : Nat, y > x :=
by sorry

example (f : Nat → Nat) (hf : ∀ x : Nat , ∃ y : Nat, f y > x) :
  ∃ g : Nat → Nat, ∀ x : Nat, (f ∘ g) x > x :=
by sorry

--advanced skolemization tests
example : ∀ x : Nat, ∀ y : Nat, ∃ z : Nat, z > x + y :=
by sorry

example {p : Prop} (hP : p) (f : Nat → Nat)
  (h' : p → p ∧ (∀ x : Nat , ∃ y : Nat, f y > x)) :
  ∃ g : Nat → Nat, ∀ x : Nat, (f ∘ g) x > x :=
by sorry
