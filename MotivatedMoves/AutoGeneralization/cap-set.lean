import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector.Zip
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

def zero : ZMod 3 := 0
def one : ZMod 3 := 1
def two : ZMod 3 := 2
def func_examp : Fin 5 → ZMod 3 := ![zero,one,two,zero,one]
def vec_examp : Vector (ZMod 3) 6 := Vector.ofFn ![one,zero,one,two,zero,one]

/- Define a function that takes us from functions to vectors -/
def toVec {α : Type}  {n : ℕ} (f : Fin n → α) : Vector α n :=  Vector.ofFn f
#eval toVec func_examp

/- Define a function that takes us from vectors to functions -/
def toFunc {α : Type} {n : ℕ} (v : Vector α n) : Fin n → α := fun i => v.get i
#eval toFunc vec_examp

/- The all-zeroes vector in n-dimensions -/
-- def z {n : ℕ} : Vector (ZMod 3) n := Vector.replicate n zero --toVec  (fun _ => 0)
-- #eval @z 5 -- the 5-dimensional all-zeroes vector
def z {n : ℕ} : Vector (ZMod 3) n := Vector.replicate n zero --⟨List.replicate n zero, by simp⟩
#eval @z 5 -- the 5-dimensional all-zeroes vector

/- A basis vector in n-dimensions -/
def e {n : ℕ} (i : Fin n) : Vector (ZMod 3) n := Vector.set (@z n) i 1
#eval e (3 : Fin 5) -- a 5-dimensional basis vector with a "one" at the 3rd index

/- A 1-d vector-/
def dim1Vector {α : Type} (a : α): Vector α 1:= ⟨[a], rfl⟩
#eval dim1Vector one

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

/- Allow "++" notation to append vectors -/
instance  {α : Type} {n m : ℕ} : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) :=
  ⟨Vector.append⟩

/- Define a function that sums all coordinates of a vector -/
-- def sum {n : ℕ} (v : Vector (ZMod 3) n) : ZMod 3 := Finset.sum (Finset.univ) (toFunc v) -- v.1.sum -- v.toList.sum
-- #eval vec_examp -- [1, 0, 1, 2, 0, 1]
-- #eval sum vec_examp -- 1

/- The sum of a vector is the sum of the head + sum of its tail -/
-- def sum {n : ℕ} (v : Vector (ZMod 3) n): ZMod 3 :=
--   match v with
--   | ⟨h :: t, _⟩   => h + List.sum t
--   | ⟨[], _ ⟩      => 0
-- #eval vec_examp -- [1, 0, 1, 2, 0, 1]
-- #eval sum vec_examp -- 2

-- def sum {n : ℕ} (v : Vector (ZMod 3) n): ZMod 3 :=
--   match v with
--   | Vector (ZMod 3) 0 => sorry
--   | Vector (ZMod 3) 1 => sorry
--   | Vector.cons h t   => sorry
--   -- v.head + (List.sum v.tail.1)
-- #eval vec_examp -- [1, 0, 1, 2, 0, 1]
-- #eval sum vec_examp -- 2

def sum {n : ℕ} (v : Vector (ZMod 3) n): ZMod 3 := List.sum (Vector.toList v)
#eval vec_examp -- [1, 0, 1, 2, 0, 1]
#eval sum vec_examp -- 2

-- lemma h : List.map (toFunc x) (Finset.toList Finset.univ) = Vector.toList x := by
--   simp [toFunc]
--   simp [Vector.get]
--   simp [Finset.toList]
--   simp [Vector.toList]
--   sorry

-- lemma finset_sum_is_list_sum {n : ℕ} {x : Vector (ZMod 3) n}: Finset.sum Finset.univ (toFunc x) = x.toList.sum :=
-- by
--   have := Eq.symm $ Finset.sum_to_list Finset.univ (toFunc x)
--   rw [← h]
--   apply (Eq.symm $ Finset.sum_to_list Finset.univ (toFunc x))

-- #check List.sum_toFinset
-- #check Finset.sum_to_list

-- /- Lemma to allow conversion between vectors and functions -/
-- lemma ith_of_vec_is_ith_of_func : Vector.get (toVec f) i = f i :=
--   by {
--     rw [toVec, Vector.get]
--     show List.nthLe
--     simp
--   }

-- theorem Vector.sum_set' {n : ℕ} {α : Type u_1} [AddCommGroup α] (v : Vector α n) (i : Fin n) (a : α) :
-- List.sum (Vector.toList (Vector.set v i a)) = List.sum (Vector.toList v) + -Vector.get v i + a


/- Lemma: the sum of all components of a basis vector is 1 -/
def sum_of_basis_vec_is_one : ∀ i : Fin n, sum (e i) = 1 := by
  intro i
  simp only [sum, e, z, zero]
  rw [Vector.sum_set']
  simp [Vector.get_replicate]
  simp [Vector.replicate]


-- Define the sets A₀, A₁, A₂ based on the sum of components modulo 3
-- def A₀ (n : ℕ) : Finset (Vector (ZMod 3) n) :=  { x // sum x = 0}
def A₀ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => sum v = 0) Finset.univ
def A₁ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => sum v = 1) Finset.univ
def A₂ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.filter (fun v => sum v = 2) Finset.univ
#eval (toVec ![zero, zero, zero, zero, zero]) ∈ A₀ 5 -- true
#eval (toVec ![zero, zero, zero, zero, one]) ∈ A₀ 5 -- false

-- Define the vector space of n dimensional vectors over ZMod 3
def 𝔽₃ (n : ℕ) : Finset (Vector (ZMod 3) n) := Finset.univ

lemma card_of_𝔽₃' (n : ℕ) : Fintype.card (Vector (ZMod 3) n) = 3 ^ n := by
  apply card_vector

lemma card_of_𝔽₃ (n : ℕ) : Fintype.card { x // x ∈ 𝔽₃ n } = 3^n := by
  have h := card_of_𝔽₃' n
  simp
  assumption

/- Given an n-dimensional vector, we can create an (n+1)-dim vector with coord sum 0 -/
lemma can_create_vector_with_sum_0 (v : { x // x ∈ 𝔽₃ n }):
  (-(sum v.val)) ::ᵥ v.val ∈ A₀ (n + 1) := by
  have := -(sum v.val)+ (sum v.val) = 0 := by sorry

/- The function that takes any vector, and turns it into a vector in the bigger space with sum 0 mod 3  -/
def f (n : ℕ) : { x // x ∈ 𝔽₃ n } → { x // x ∈ A₀ (n + 1) }  :=
  fun v => ⟨(-(sum v.val)) ::ᵥ v.val, by apply can_create_vector_with_sum_0⟩

theorem f_injective (n : ℕ)  : Function.Injective (f n) := by sorry

/- Remove the last element of a vector-/
abbrev removeFirst {α : Type} {n : ℕ} ( v : Vector α (n+1)) : Vector α n :=
  v.tail
#eval removeFirst (Vector.ofFn ![zero, one, two])

lemma vector_in_A0_has_sum_0 {n : ℕ} (b: { x // x ∈ A₀ (n+1) }) :
  sum b.val = 0 := by
  simp [A₀] at b

#check Subtype.val_prop
#check Subtype.coe_prop ↑b

lemma first_val_of_vec_in_A0_is_unique {n : ℕ} (b: { x // x ∈ A₀ (n+1) }) :
  b.val.head = -sum b.val.tail := by
  have hb := vector_in_A0_has_sum_0 b
  rw [sum] at hb
  simp

  -- have : sum b.val = 0 := by simp [Subtype.ext_val]
  -- have h :  (b.val.head) + (sum b.val.tail) = sum b.val := by simp [sum]
  -- have :  (b.val.head) + (sum b.val.tail) = 0 := by simp [h]

/- Prove that removing the last element of a list then adding it back gives the same list-/
theorem truncate_then_apply_f_keeps_same {n : ℕ} (b: { x // x ∈ A₀ (n+1) }) :
  b = f n ⟨(removeFirst b.val), by simp [𝔽₃]⟩ := by
  have hb := first_val_of_vec_in_A0_is_unique b
  match b with
  | ⟨⟨[], pf⟩, _⟩ => simp at pf; contradiction
  | ⟨⟨h :: t, _⟩, _⟩ =>
    simp [removeFirst, Vector.tail, f]
    apply Subtype.ext_val -- if the two vals of a subtype are equal, the two subtypes are qual
    simp [Vector.head] at hb ⊢
    assumption

theorem f_surjective (n : ℕ)  : Function.Surjective (f n) := by
  unfold Function.Surjective
  intro b -- consider an arbitrary element in  A₀ (n + 1)
  use ⟨removeFirst b.val, by {simp [𝔽₃]}⟩ -- show that it is reachable by applying f to its truncated form
  have h := truncate_then_apply_f_keeps_same b
  rw [← h]

/- There's a bijection between vectors that have sum 0 mod 3 in the (n+1)-dim vector space, and all vectors in the n-dim vector space -/
theorem f_bijective (n : ℕ) : Function.Bijective (f n) := by
  unfold Function.Bijective
  constructor
  apply f_injective n
  apply f_surjective n

/- These spaces have the same size: vectors that have sum 0 mod 3 in the (n+1)-dim vector space, and all vectors in the n-dim vector space -/
lemma card_of_A₀_is_card_of_full_smaller_vec_space (n : ℕ)  : Fintype.card (𝔽₃ n) = Fintype.card (A₀ (n+1))  := by
  apply Fintype.card_of_bijective (f_bijective n)

/- The fintype version: the number of elements of 𝔽₃(n) have coordinate-sum equal to 0 mod 3. -/
lemma card_of_A₀' (n : ℕ) :  Fintype.card (A₀ (n+1)) = 3^n := by
  rw [← card_of_𝔽₃ n]
  apply (Eq.symm $ card_of_A₀_is_card_of_full_smaller_vec_space n )

/- The finset version: the number of elements of 𝔽₃(n) have coordinate-sum equal to 0 mod 3. -/
lemma card_of_A₀ (n : ℕ) :  Finset.card (A₀ (n+1)) = 3^n := by
  have h := card_of_A₀' n; simp [Fintype.card] at h
  assumption

/- A third of the vectors in 𝔽₃(n) have coordinate-sum equal to 0 mod 3. -/
lemma partition_has_density_one_third : ∀ n : ℕ, n ≥ 1 → density (A₀ n) = 1/3 := by
  intro n h
  rw [density]
  induction' n with N _
  · contradiction
  · rw [card_of_A₀]
    field_simp; rw [← @pow_succ']

/- If you have a vector x and a vector y, then sum(x+y) = sum(x) + sum(y) -/
lemma sum_of_vector_sum_is_sum_of_sum_of_vectors {n : ℕ} {x : Vector (ZMod 3) n} {y : Vector (ZMod 3) n} :
 sum x + sum y = sum (x+y):=
by
  simp only [sum, finset_sum_is_list_sum]
  apply Vector.sum_add_sum_eq_sum_zipWith x

/- If you have a vector x ∈ A₀ (coordinate-sum 0), then x + e i ∈ A₁ (coordinate-sum 1) -/
lemma adding_basis_vector_puts_in_higher_slice {n : ℕ} {x : Vector (ZMod 3) n} :
  x ∈ A₀ n →  (∀ i : Fin n, x + e i ∈ A₁ n) :=
by
  intros h i
  simp [A₀, A₁] at *
  simp [← sum_of_vector_sum_is_sum_of_sum_of_vectors, h]
  apply sum_of_basis_vec_is_one i

/- Weaker lemma: if you have a vector x ∈ A₀ (coordinate-sum 0), then x + e i ∉ A₀ -/
lemma adding_basis_vector_changes_slice {n : ℕ} {x : Vector (ZMod 3) n} :
  x ∈ A₀ n →  (∀ i : Fin n, x + e i ∉ A₀ n) :=
by
  intros h i
  have sum1 := @adding_basis_vector_puts_in_higher_slice n x h i
  simp [A₀, A₁] at *
  by_contra sum0
  rw [sum1] at sum0
  simp at sum0

/-
A conjecture that you can create a particular line by varying only one coordinate
This disproof says that
  there's some density where some subset A can have that density,
  but A contains no such line.
-/
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
