import Tidying

-- Check we've imported tidying correctly
#eval secret

example {a b c : Nat} (h : a + b = b + a): (a + b) + c = a + (b + c):= by
  trace_state
  tidy_everything
  apply Nat.add_assoc
