import Lean
import Mathlib.Tactic

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic4000
open Autogeneralize

def Int.mod_decreasing {a b : ℤ}: a ≠ 0 → |b % a| < |a| := by
  intro a_neq_0
  rw [abs_of_nonneg (a := b % a)]
  rw [← emod_abs]
  refine emod_lt_of_pos b ?w₂.H
  rwa [@abs_pos]
  exact emod_nonneg b a_neq_0

def Int.mod_dvd {a b k : ℤ}: k ∣ b % a → k ∣ a → k ∣ b := by
  intros h1 h2
  rw [← Int.ediv_add_emod b a]
  refine Int.dvd_add ?_ h1
  exact Dvd.dvd.mul_right h2 (b / a)

def Int.dvd_mod {a b c : ℤ} : c ∣ a → c ∣ b → c ∣ (b % a) := by
  intro c_div_a c_div_b
  rw [← Int.ediv_add_emod b a] at c_div_b
  have c_div_aq: c ∣ a*(b/a) := Dvd.dvd.mul_right c_div_a (b/a)

  exact (Int.dvd_iff_dvd_of_dvd_add c_div_b).mp c_div_aq

/-- The greatest common divisor of two integers. -/
def Int.hcf (a b : ℤ) : {g : ℤ // g ∣ a ∧ g ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g)} :=
  if h:a = (0 : ℤ) then
    ⟨b, ⟨by simp_all only [dvd_zero], by simp only [dvd_refl], by simp⟩⟩
  else
    let ⟨val, ⟨ha, hb, hdiv⟩⟩ := Int.hcf (b % a) a
    ⟨val, ⟨hb, Int.mod_dvd ‹_› ‹_›, fun c hca hcr ↦ hdiv c (Int.dvd_mod ‹_› ‹_›) hca⟩⟩
  termination_by (abs a).natAbs
  decreasing_by (
    have := Int.mod_decreasing h (b:=b)
    refine natAbs_lt_natAbs_of_nonneg_of_lt ?w₁ this
    exact abs_nonneg (b % a)
  )
#print Int.hcf
#print Int.hcf._unary
example : True := by
  -- autogeneralize Int in Int.dvd_mod
  -- autogeneralize Int in Int.mod_dvd
  autogeneralize Int in Int.hcf._unary
  specialize Int.hcf._unary.Gen Nat
  trivial

#check Bool.rec
#check Nat.rec
