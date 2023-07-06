"""
Proof-dependent generalization
As described in paper 'Generalization in Type Theory Based Proof Assistants' 
"""

/---------------------------------------------------------------------------
A theorem that uses associativity and commutativity of multiplication
---------------------------------------------------------------------------/
theorem multPermute : ∀ (n m p : Nat), n * (m * p) = m * (n * p) := by
  intros n m p
  rw [← Nat.mul_assoc]
  rw [@Nat.mul_comm n m]
  rw [Nat.mul_assoc]
#print multPermute -- the proof term


/---------------------------------------------------------------------------
A generalization of the theorem to any binary operation that is assoc & comm
---------------------------------------------------------------------------/
theorem fPermute :  
∀ (f : Nat → Nat → Nat) 
-- (f_assoc : ∀ (n m p : Nat),  f n (f m p) = f (f n m) p ) -- n (m p) = (n m) p
(f_assoc : ∀ (n m p : Nat),  f (f n m) p = f n (f m p)) -- n (m p) = (n m) p
(f_comm : ∀ (n m : Nat), f n m = f m n)
(n m p : Nat), f n (f m p) = f m (f n p) -- n (m p) = m (n p) 
:= by
  intros f f_assoc f_comm n m p
  rw [← f_assoc]
  rw [f_comm n m]
  rw [f_assoc]

/---------------------------------------------------------------------------
Checking that we can instantiate the generalization with addition
---------------------------------------------------------------------------/
theorem addPermute : ∀ (n m p : Nat), n + (m + p) = m + (n + p) := by
  apply fPermute _ Nat.add_assoc Nat.add_comm
