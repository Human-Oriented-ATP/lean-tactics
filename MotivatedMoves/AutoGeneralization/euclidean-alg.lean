import Lean

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic4000
open Autogeneralize

#check Nat.gcd

--------------------------------------------------
----------- DEFINING THE GCD ALGORITHM -----------
--------------------------------------------------
def gcd (m n : @& Nat) : Nat :=
  if m = 0 then
    n
  else
    gcd (n % m) m
  termination_by m
  decreasing_by simp_wf; apply Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _); assumption

#eval gcd 90 75


--------------------------------------------------
-- PROVING CORRESPONDANCE TO THE GCD DEFINITION --
--------------------------------------------------
theorem gcd.induction {P : Nat → Nat → Prop} (m n : Nat)
    (H0 : ∀n, P 0 n) (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) : P m n :=
  Nat.strongRecOn (motive := fun m => ∀ n, P m n) m
    (fun
    | 0, _ => H0
    | _+1, IH => fun _ => H1 _ _ (Nat.succ_pos _) (IH _ (Nat.mod_lt _ (Nat.succ_pos _)) _) )
    n

theorem gcd_succ (x y : Nat) : gcd (Nat.succ x) y = gcd (y % Nat.succ x) (Nat.succ x) := by
  rw [gcd]; rfl

theorem gcd_zero_left (y : Nat) : gcd 0 y = y := by
  rw [gcd]; rfl

theorem gcd_zero_right (n : Nat) : gcd n 0 = n := by
  cases n with
  | zero => simp [gcd_succ, gcd_zero_left]
  | succ n =>
    -- `simp [gcd_succ]` produces an invalid term unless `gcd_succ` is proved with `id rfl` instead
    rw [gcd_succ]
    exact gcd_zero_left _
instance : Std.LawfulIdentity gcd 0 where
  left_id := gcd_zero_left
  right_id := gcd_zero_right

theorem gcd_rec (m n : Nat) : gcd m n = gcd (n % m) m :=
  match m with
  | 0 => by have := (Nat.mod_zero n).symm; rwa [gcd, gcd_zero_right]
  | _ + 1 => by simp [gcd_succ]

theorem gcd_dvd (m n : Nat) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) := by
  induction m, n using gcd.induction with
  | H0 n => rw [gcd_zero_left]; exact ⟨Nat.dvd_zero n, Nat.dvd_refl n⟩
  | H1 m n _ IH => rw [← gcd_rec] at IH; exact ⟨IH.2, (Nat.dvd_mod_iff IH.2).1 IH.1⟩

theorem dvd_gcd : k ∣ m → k ∣ n → k ∣ gcd m n := by
  induction m, n using gcd.induction with intro km kn
  | H0 n => rw [gcd_zero_left]; exact kn
  | H1 n m _ IH => rw [gcd_rec]; exact IH ((Nat.dvd_mod_iff km).2 kn) km

theorem gcd_def_iff_gcd_alg (m n : Nat): (gcd m n ∣ m) ∧ (gcd m n ∣ n) ∧ (k ∣ m → k ∣ n → k ∣ gcd m n ) := by
  constructor
  apply (gcd_dvd m n).left
  constructor
  apply (gcd_dvd m n).right
  apply dvd_gcd

example : True := by
  autogeneralize Nat in gcd_def_iff_gcd_alg
  trivial
