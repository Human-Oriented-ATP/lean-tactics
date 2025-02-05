import Lean
import Mathlib.Tactic

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic4000
open Autogeneralize

-- #check Int.dvd_mod_iff

def Int.dvd_mod (a b c : ℤ) : c ∣ a → c ∣ b → c ∣ (b % a) := by
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
    ⟨val, ⟨hb, sorry, fun c hca hcr ↦ hdiv c sorry hca⟩⟩
  termination_by a
  decreasing_by sorry
