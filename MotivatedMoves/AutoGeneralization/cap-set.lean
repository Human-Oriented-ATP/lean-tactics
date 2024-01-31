import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector.Zip

def zero : ZMod 3 := 0
def one : ZMod 3 := 1
def two : ZMod 3 := 2
def vec_examp : Vector (ZMod 3) 5 := ⟨[zero,one,two,zero,one], by simp⟩
def func_examp : Fin 5 → ZMod 3 := ![zero,one,two,zero,one]

/- Define a function that takes us from functions to vectors -/
def toVec {n : ℕ} (f : Fin n → ZMod 3) : Vector (ZMod 3) n :=  ⟨List.ofFn f, by simp⟩
#eval toVec func_examp

/- Define a function that takes us from vectors to functions -/
def toFunc {n : ℕ} (v : Vector (ZMod 3) n) : Fin n → ZMod 3 := fun i => v.get i
#eval toFunc vec_examp

/- The all-zeroes vector in n-dimensions -/
def z {n : ℕ} : Vector (ZMod 3) n := toVec  (fun _ => 0)
#eval @z 5 -- the 5-dimensional all-zeroes vector

/- A basis vector in n-dimensions -/
def e  {n : ℕ} (i : Fin n) : Vector (ZMod 3) n := toVec (fun idx => if idx == i then 1 else 0)
#eval e (3 : Fin 5) -- a 5-dimensional basis vector with a "one" at the 3rd index

/- The density of any subset A in the finite field -/
noncomputable def density {n : ℕ} (A : Finset (Vector (ZMod 3) n)) : ℝ  :=  A.card / 3^n

#check Vector.zipWith

/- Define what addition looks like for two vectors-/
instance : Add (Vector (ZMod 3) n) :=
  ⟨Vector.zipWith (fun x y => x + y)⟩
  -- ⟨Vector.map₂ Add.add⟩
#eval e (2 : Fin 5) + e (1 : Fin 5)

/- Define what scaling looks like for a vectors-/
instance : HMul ℕ (Vector (ZMod 3) n) (Vector (ZMod 3) n) := ⟨fun a v => v.map (fun x => a * x)⟩
#eval 2 *  e (1 : Fin 5) -- [0, 2, 0, 0, 0]
#eval 3 *  e (1 : Fin 5) -- zeroes out (because we're going mod 3)[0, 0, 0, 0, 0]

/- Define a function that sums all coordinates of a vector -/
def sum {n : ℕ} (v : Vector (ZMod 3) n) : ZMod 3 := v.toList.sum
#eval vec_examp -- [0, 1, 2, 0, 1]
#eval sum vec_examp -- 1

-- Define the sets A₀, A₁, A₂ based on the sum of components modulo 3
def A₀ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => sum v = 0) Finset.univ
def A₁ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => sum v = 1) Finset.univ
def A₂ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => sum v = 2) Finset.univ
#eval (toVec ![zero, zero, zero, zero, zero]) ∈ A₀ 5 -- true
#eval (toVec ![zero, zero, zero, zero, one]) ∈ A₀ 5 -- false

/- Lemma: if you have a vector x and a vector y, then sum(x+y) = sum(x) + sum(y) -/
lemma sum_of_vector_sum_is_sum_of_sum_of_vectors {n : ℕ} {x : Vector (ZMod 3) n} {y : Vector (ZMod 3) n} :
 sum x + sum y = sum (x+y):=
by
  apply Vector.sum_add_sum_eq_sum_zipWith x y

/- Lemma: if you have a vector x ∈ A₀, then x + e i ∉ A₀ -/
lemma adding_basis_vector_changes_slice {n : ℕ} {x : Vector (ZMod 3) n} :
  x ∈ A₀ n →  (∀ i : Fin n, x + e i ∈ A₁ n) :=
by
  intro h
  intro i
  rw A₀ at h
  simp at h
  rw A₁
  exact h




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

  -- Prove the set A₀ works
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
