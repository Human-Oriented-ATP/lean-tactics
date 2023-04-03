import Tidying
import InfoDisplayTactics

example {a b : Nat} (h : a + b = b + a) : (a + b = b + a) := by
  trace_state
  tidy_target
  trace_state
  tidy_declarations
  trace_state
  apply h

example {a b c : Nat} (h : a + b = b + a) :
    ((a + b) + c = a + (b + c)) ∧ (a + b = b + a) := by
  apply And.intro
  trace_state
  tidy_all
  trace_state
  tidy_everything
  trace_state
  apply Nat.add_assoc
  apply h
