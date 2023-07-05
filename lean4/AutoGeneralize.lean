
theorem multPermute : ∀ (n m p : Nat), n * (m * p) = m * (n * p) := by
  intros n m p
  rw [← Nat.mul_assoc]
  rw [@Nat.mul_comm n m]
  rw [Nat.mul_assoc]
