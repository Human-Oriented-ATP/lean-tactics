import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Real.Basic

/- The all-zeroes vector in n-dimensions -/
def z {n : ℕ} : Fin n → Fin 3 := fun _idx => 0
#eval (z : Fin 10 → Fin 3)
#eval (z : Fin 10 → Fin 3) 3

/- A basis vector in n-dimensions -/
def e  {n : ℕ} (i : Fin n) : Fin n → Fin 3 := fun idx => if idx == i then 1 else 0
#eval ((e 3) : Fin 4 → Fin 3)
#eval ((e 0) : Fin 4 → Fin 3)

/- The density of any subset A in the finite field
  Note that anything of type (Fin n → Fin 3) is actually an n-dim vector taking values 0,1,2
  So A : Finset (Fin n → Fin 3) is some subset of n-dim vectors -/
noncomputable def density {n : ℕ} (A : Finset (Vector (ZMod 3) n)) : ℝ  :=  A.card / 3^n


-- Define the sets A₀, A₁, A₂ based on the sum of components modulo 3
def A₀ {n : ℕ} : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => (v.toList.sum % 3) = 0) Finset.univ
def A₁ {n : ℕ} : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => (v.toList.sum % 3) = 1) Finset.univ
def A₂ {n : ℕ} : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => (v.toList.sum % 3) = 2) Finset.univ


/- A conjecture that you can create a particular line by varying only one coordinate -/
theorem cap_set_vary_1_coord_not_true :
  ∃ (δ : ℝ), δ > 0 →
  ∀ (n : ℕ), ∃ (A : Finset (Vector (ZMod 3) n)),
    density A = δ →
    ∀ (x : Vector (ZMod 3) n) (i : Fin n),
      x ∈ A →
      (x + e i) ∉ A ∨ (x + 2 * e i) ∉ A :=
by
  use 1/3
  intros δ n

  -- Prove the existence of sets A₀, A₁, A₂
  use A₀
  intros hA x i hx

  -- Show that for any x and i in A, either (x + i) or (x + 2 * i) is also in A
  simp [density, nat.pow_pos (nat.succ_pos 2) n, hδ] at hA,
  by_cases hi : i.sum % 3 = 0,
  { left, exact finset.mem_filter.2 ⟨mem_univ _, hi⟩ },
  by_cases hi1 : i.sum % 3 = 1,
  { right, exact finset.mem_filter.2 ⟨mem_univ _, hi1⟩ },
  { left, exact finset.mem_filter.2 ⟨mem_univ _, by linarith⟩ },
  sorry
