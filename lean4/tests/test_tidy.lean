import Tidying

-- Check we;ve imported tidying correctly
#eval secret

example {a b c : Nat} : (a + b) + c = a + (b + c):= by
  trace_goal
  tidy_goal
  trace_goal
  apply Nat.add_assoc
