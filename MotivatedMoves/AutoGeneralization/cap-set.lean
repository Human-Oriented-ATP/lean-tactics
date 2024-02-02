import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector.Zip
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

def zero : ZMod 3 := 0
def one : ZMod 3 := 1
def two : ZMod 3 := 2
def func_examp : Fin 5 → ZMod 3 := ![zero,one,two,zero,one]
def vec_examp : Vector (ZMod 3) 5 := Vector.ofFn ![zero,one,two,zero,one]

/- Define a function that takes us from functions to vectors -/
def toVec {n : ℕ} (f : Fin n → ZMod 3) : Vector (ZMod 3) n :=  Vector.ofFn f
#eval toVec func_examp

/- Define a function that takes us from vectors to functions -/
def toFunc {n : ℕ} (v : Vector (ZMod 3) n) : Fin n → ZMod 3 := fun i => v.get i
#eval toFunc vec_examp

/- The all-zeroes vector in n-dimensions -/
def z {n : ℕ} : Vector (ZMod 3) n := Vector.replicate n zero --toVec  (fun _ => 0)
#eval @z 5 -- the 5-dimensional all-zeroes vector

/- A basis vector in n-dimensions -/
def e {n : ℕ} (i : Fin n) : Vector (ZMod 3) n := toVec (fun idx => if idx = i then 1 else 0)
#eval e (3 : Fin 5) -- a 5-dimensional basis vector with a "one" at the 3rd index

/- The density of any subset A in the finite field -/
noncomputable def density {n : ℕ} (A : Finset (Vector (ZMod 3) n)) : ℝ  :=  A.card / 3^n

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
def sum {n : ℕ} (v : Vector (ZMod 3) n) : ZMod 3 := Finset.sum (Finset.univ) (toFunc v) -- v.1.sum -- v.toList.sum
#eval vec_examp -- [0, 1, 2, 0, 1]
#eval sum vec_examp -- 1

lemma h : List.map (toFunc x) (Finset.toList Finset.univ) = Vector.toList x := by
  simp [toFunc]
  simp [Vector.get]
  simp [Finset.toList]
  simp [Vector.toList]
  sorry

lemma finset_sum_is_list_sum {n : ℕ} {x : Vector (ZMod 3) n}: Finset.sum Finset.univ (toFunc x) = x.toList.sum :=
by
  have := Eq.symm $ Finset.sum_to_list Finset.univ (toFunc x)
  rw [← h]
  apply (Eq.symm $ Finset.sum_to_list Finset.univ (toFunc x))

#check List.sum_toFinset
#check Finset.sum_to_list

/- Lemma to allow conversion between vectors and functions -/
lemma ith_of_vec_is_ith_of_func : Vector.get (toVec f) i = f i := by {rw [toVec, Vector.get]; simp}

/- Lemma: the sum of all components of a basis vector is 1 -/
def sum_of_basis_vec_is_one : ∀ i : Fin n, sum (e i) = 1 := by
  intro i
  simp only [sum, toFunc, e]
  simp only [ith_of_vec_is_ith_of_func, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

-- Define the sets A₀, A₁, A₂ based on the sum of components modulo 3
-- def A₀ (n : ℕ) : Finset (Vector (ZMod 3) n) :=  { x // sum x = 0}
def A₀ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => sum v = 0) Finset.univ
def A₁ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => sum v = 1) Finset.univ
def A₂ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => sum v = 2) Finset.univ
#eval (toVec ![zero, zero, zero, zero, zero]) ∈ A₀ 5 -- true
#eval (toVec ![zero, zero, zero, zero, one]) ∈ A₀ 5 -- false

-- Define the vector space of n dimensional vectors over ZMod 3
def 𝔽₃ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.univ

lemma card_of_𝔽₃' (n : ℕ) : Fintype.card (Vector (ZMod 3) n) = 3 ^ n := by apply card_vector

lemma card_of_𝔽₃ (n : ℕ) : Fintype.card { x // x ∈ 𝔽₃ n } = 3^n := sorry

-- def f {n : ℕ} : Vector (ZMod 3) (n) → Vector (ZMod 3) (n+1) := fun v => (Vector.append v (Vector.ofFn ![3-sum v]))

def f (n : ℕ) : { x // x ∈ A₀ (n + 1) } → { x // x ∈ 𝔽₃ n } := sorry--fun v => (Vector.append v (Vector.ofFn ![3-sum v]))

theorem f_bij (n : ℕ): Function.Bijective (f n) := by sorry
-- or could use Finset.card_congr

lemma card_of_A₀_is_card_of_full_smaller_vec_space (n : ℕ) :  Fintype.card (A₀ (n+1)) = Fintype.card (𝔽₃ n) := by
  apply Fintype.card_of_bijective (f_bij n)

lemma card_of_A₀' (n : ℕ) :  Fintype.card (A₀ (n+1)) = 3^n := by
  -- have card := @card_of_A₀_is_card_of_full_smaller_vec_space n
  rw [← card_of_𝔽₃ n]
  apply (card_of_A₀_is_card_of_full_smaller_vec_space n)

def hasSum0 {n : ℕ} : { x // x ∈ A₀ (n + 1) } → Prop := fun v => sum v == 0

-- theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
--     @card { x // p x } (Fintype.subtype s H) = s.card :=
--   Multiset.card_pmap _ _ _

-- theorem pf :  ∀ v : { x // x ∈ A₀ (n + 1) }, v ∈ (A₀ (n+1)) ↔ hasSum0 v := by
  -- sorry

example (n : ℕ) : n ≥ 1 → n - 1 + 1 = n := by
  intros h
  refine Nat.sub_add_cancel h

lemma card_of_A₀ (n : ℕ) :  Finset.card (A₀ (n+1)) = 3^n := by sorry

  -- have := Fintype.subtype_card (A₀ (n+1)) _
  -- have := subtype_card (A₀ (n+1))
  -- apply (card_of_A₀_is_card_of_full_smaller_vec_space n)


example (n : ℕ ) : n ≥ 1 → n - (n - 1) = 1 := by exact fun a => Nat.sub_sub_self a

lemma partition_has_density_one_third : ∀ n : ℕ, n ≥ 1 → density (A₀ n) = 1/3 := by
  intro n h
  rw [density]
  induction' n
  · contradiction
  · rw [card_of_A₀]
    field_simp
    rw [← @pow_succ']
    norm_cast

/- Lemma: if you have a vector x and a vector y, then sum(x+y) = sum(x) + sum(y) -/
lemma sum_of_vector_sum_is_sum_of_sum_of_vectors {n : ℕ} {x : Vector (ZMod 3) n} {y : Vector (ZMod 3) n} :
 sum x + sum y = sum (x+y):=
by
  simp only [sum, finset_sum_is_list_sum]
  apply Vector.sum_add_sum_eq_sum_zipWith x

/- Lemma: if you have a vector x ∈ A₀, then x + e i ∉ A₀ -/
lemma adding_basis_vector_changes_slice' {n : ℕ} {x : Vector (ZMod 3) n} :
  x ∈ A₀ n →  (∀ i : Fin n, x + e i ∈ A₁ n) :=
by
  intros h i
  simp [A₀, A₁] at *
  simp [← sum_of_vector_sum_is_sum_of_sum_of_vectors, h]
  apply sum_of_basis_vec_is_one i

lemma adding_basis_vector_changes_slice {n : ℕ} {x : Vector (ZMod 3) n} :
  x ∈ A₀ n →  (∀ i : Fin n, x + e i ∉ A₀ n) :=
by
  intros h i
  have sum1 := @adding_basis_vector_changes_slice' n x h i
  simp [A₀, A₁] at *
  by_contra sum0
  rw [sum1] at sum0
  simp at sum0


/- A conjecture that you can create a particular line by varying only one coordinate -/
theorem cap_set_basis_size_1_disproof :
  ∃ (δ : ℝ), δ > 0 →
  ∀ (n : ℕ), n ≥ 1 →
  ∃ (A : Finset (Vector (ZMod 3) n)),
    density A = δ ∧
    ∀ (x : Vector (ZMod 3) n) (i : Fin n),
      x ∈ A →
      (x + e i) ∉ A ∨ (x + 2 * e i) ∉ A :=
by
  use 1/3 -- We need to prove the density 1/3 works
  intros _δ n hn
  use A₀ n -- We need to prove the set A₀ works
  constructor
  apply partition_has_density_one_third n hn
  intros x i hx; left;
  apply adding_basis_vector_changes_slice hx
