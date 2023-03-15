import tactic

------------------------------------------------
-- Tag allowable graph theory theorems --
------------------------------------------------
@[user_attribute]
meta def dummy : user_attribute :=
{ name := `dummy,
  descr := "A tag for all silly theorems for debugging purposes." }

------------------------------------------------
-- The allowable theorems --
------------------------------------------------
-- A sample there-exists statement for debugging
@[dummy] 
theorem exists_one: 
  ∃ n : ℕ, n=1 :=
begin
  use 1
end

-- A sample for-all, there-exists statement for debugging
@[dummy] 
theorem forall_exists_greater: 
  ∀ n : ℕ, ∃ k : ℕ, k = n+1 :=
begin
  intros n, use n+1,
end