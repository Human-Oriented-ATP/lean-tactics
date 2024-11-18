import Mathlib.Tactic
import MotivatedMoves.Mirek.SmtHammer.Solver

def countWindowN (l : List Bool) (x0 : ℕ) (x1 : ℕ) : ℕ
  := ((l.drop x0).take (x1-x0)).count true

def countWindow (l : List Bool) (x0 x1 : ℤ) : ℕ
  := countWindowN l x0.toNat x1.toNat

theorem list_drop_drop (l : List Bool) (a b : ℕ)
: l.drop (a+b) = (l.drop a).drop b
:= by
  induction b
  · rfl
  · simp [add_comm]

theorem count_window_n_add (l : List Bool) (x0 x1 x2 : ℕ)
: x0 ≤ x1 → x1 ≤ x2
→ countWindowN l x0 x1 + countWindowN l x1 x2
  = countWindowN l x0 x2
:= by
  intros h01 h12
  unfold countWindowN
  rw [←List.count_append]
  apply congrArg
  have : x1 = (x1 - x0) + x0 := (Nat.sub_eq_iff_eq_add h01).mp rfl
  conv in (List.drop x1 l) => rw [this]
  rw [←List.drop_drop]
  set l2 := l.drop x0
  have : x2 - x0 = (x1 - x0) + (x2 - x1) := by omega
  rw [this]
  exact (List.take_add l2 (x1 - x0) (x2 - x1)).symm

theorem count_window_add (l : List Bool) (x0 x1 x2 : ℤ)
: x0 ≤ x1 → x1 ≤ x2
→ countWindow l x0 x1 + countWindow l x1 x2
  = countWindow l x0 x2
:= by
  unfold countWindow
  intros h1 h2
  apply count_window_n_add
  exact Int.toNat_le_toNat h1
  exact Int.toNat_le_toNat h2

theorem count_window_add0 (l : List Bool) (x0 x1 : ℤ)
: x0 ≤ x1
→ countWindow l 0 x0 + countWindow l x0 x1
  = countWindow l 0 x1
:= by
  unfold countWindow
  intro h
  simp
  apply count_window_n_add l 0 x0.toNat x1.toNat
  exact Nat.zero_le x0.toNat
  exact Int.toNat_le_toNat h

theorem ineq_chain_plus (f : ℤ → ℤ) (a : ℤ) (b : ℕ)
: (∀ (n : ℤ), a ≤ n → n < a+b → f n < f (n+1))
→ f (a+b) ≥ f a + b
:= by
  induction b with
  | zero => simp
  | succ b ih =>
    intro h
    have h_last := h (a+b) (by omega) (by omega)
    have ih2 := ih (by
      intro n; intros
      apply h; assumption; omega
    )
    have : b.succ = b+1 := by rfl
    simp [this, ←add_assoc]
    omega

theorem ineq_chain (f : ℤ → ℤ) (a b : ℤ)
: a ≤ b → (∀ (n : ℤ), a ≤ n → n < b → f n < f (n+1))
→ f b ≥ f a + (b-a)
:= by
  intros h1 h2
  let c := (b-a).toNat
  have : ↑c = (b-a) := Int.toNat_sub_of_le h1
  have : b = a+c := by simp [this]
  simp [this]
  rw [this] at h2
  exact ineq_chain_plus f a c h2

example (l : List Bool) : l.count true ≤ l.length := by exact List.count_le_length true l

theorem count_window_n_basic_bound (l : List Bool) (x0 : ℕ) (x1 : ℕ)
: x0 ≤ x1 → x0 + countWindowN l x0 x1 ≤ x1
:= by
  intro h
  unfold countWindowN
  have := List.count_le_length true ((l.drop x0).take (x1-x0))
  have := List.length_take_le (x1 - x0) (l.drop x0)
  omega

theorem count_window_basic_bound (l : List Bool) (x0 x1 : ℤ)
: x0 ≤ x1 → countWindow l x0 x1 ≤ x1 - x0
:= by
  unfold countWindow
  intro h1
  have := count_window_n_basic_bound l x0.toNat x1.toNat (Int.toNat_le_toNat h1)
  cases x0 with
  | ofNat x0n =>
    simp at *
    cases x1 with
    | ofNat x1n =>
      simp at *
      omega
    | negSucc x1n =>
      simp [Int.toNat, countWindowN, h1]
  | negSucc x0n =>
    cases x1 with
    | ofNat x1n =>
      simp [Int.toNat] at *
      have : Int.negSucc x0n = -(x0n+1) := rfl
      omega
    | negSucc x1n =>
      simp [Int.toNat, countWindowN, h1]

theorem count_window_n_zero (l : List Bool) (x0 x1 : ℕ)
: x0 ≥ x1 → countWindowN l x0 x1 = 0
:= by
  intro h
  unfold countWindowN
  have : x1 - x0 = 0 := Nat.sub_eq_zero_of_le h
  simp [this]

theorem count_window_zero (l : List Bool) (x0 x1 : ℤ)
: x0 ≥ x1 → countWindow l x0 x1 = 0
:= by
  intro h
  unfold countWindow
  apply count_window_n_zero
  exact Int.toNat_le_toNat h

theorem count_window_zero0 (l : List Bool) (x0 : ℤ)
: countWindow l x0 0 = 0
:= by
  unfold countWindow
  apply count_window_n_zero
  simp

def problem_assump (n : ℤ) (l : List Bool) : Prop :=
  l.length = n^2 + n ∧ n ≥ 0 ∧
  ∀ k : ℤ, 0 ≤ k → k ≤ n^2-n →
    countWindow l k (k+n) < countWindow l (k+n) (k+2*n)

theorem problem_window_al_lower_bound (n : ℤ) (l : List Bool)
: problem_assump n l → ∀ k : ℤ, 0 ≤ k → k ≤ n →
  countWindow l (n*k) (n*k + n) ≥ k
:= by
  intro ⟨h1,h2,h3⟩
  intros k k0 kn
  have := ineq_chain (λ x : ℤ ↦ countWindow l (n*x) (n*x + n)) 0 k k0 (by
    intros x _ _; simp
    have ineq := h3 (n * x)
    ring_nf at *
    int_hammer
  )
  simp at this
  apply le_trans; swap; exact this
  omega

theorem problem_window_al_upper_bound (n : ℤ) (l : List Bool)
: problem_assump n l → ∀ k : ℤ, 0 ≤ k → k ≤ n →
  countWindow l (n*k) (n*k + n) ≤ k
:= by
  intro ⟨h1,h2,h3⟩
  intros k k0 kn
  have := ineq_chain (λ x : ℤ ↦ countWindow l (n*x) (n*x + n)) k n kn (by
    intros x _ _; simp [mul_add]
    have := h3 (n*x)
    ring_nf at *
    int_hammer
  )
  simp at this
  have := count_window_basic_bound l (n * n) (n * n + n)
  omega

theorem problem_window_al_value (n : ℤ) (l : List Bool)
: problem_assump n l → ∀ k : ℤ, 0 ≤ k → k ≤ n →
  countWindow l (n*k) (n*k + n) = k
:= by
  intros h k k0 kn
  apply Int.le_antisymm
  apply problem_window_al_upper_bound n l h k k0 kn
  apply problem_window_al_lower_bound n l h k k0 kn

theorem problem_window_nal_lower_bound (n : ℤ) (l : List Bool)
: problem_assump n l → ∀ a : ℤ, 0 ≤ a → a < n → ∀ k : ℤ, 0 ≤ k → k < n →
  countWindow l (n*k + a) (n*k + n + a) ≥ k
:= by
  intro ⟨h1,h2,h3⟩
  intros a a0 an k k0 kn
  have := ineq_chain (λ x : ℤ ↦ countWindow l (n*x+a) (n*x+a+n))
    0 k k0
    (by
      intros x _ _
      simp
      have := h3 (n*x+a)
      ring_nf at *
      int_hammer
    )
  simp at this
  have : n * k + n + a = n * k + a + n := by linarith
  rw [this]
  omega

theorem problem_window_nal_upper_bound (n : ℤ) (l : List Bool)
: problem_assump n l → ∀ a : ℤ, 0 ≤ a → a < n → ∀ k : ℤ, 0 ≤ k → k < n →
  countWindow l (n*k + a) (n*k + n + a) ≤ k+1
:= by
  intro ⟨h1,h2,h3⟩
  intros a a0 an k k0 kn
  have := ineq_chain (λ x : ℤ ↦ countWindow l (n*x+a) (n*x+a+n))
    k (n-1) (Int.le_sub_one_of_lt kn)
    (by
      intros x _ _
      simp
      have := h3 (n*x+a)
      ring_nf at *
      int_hammer
    )
  simp at this
  have := count_window_basic_bound l (n * (n-1) + a) (n*n + a)
  ring_nf at *
  omega

theorem problem_window_nal_value (n : ℤ) (l : List Bool)
: problem_assump n l → ∀ a : ℤ, (0 ≤ a ∧ a < n) → ∀ k : ℤ, 0 ≤ k → k < n →
  countWindow l (n*k+a) (n*k+n+a) = k ∨ countWindow l (n*k+a) (n*k+n+a) = k+1
:= by
  intro h a ⟨a0,an⟩ k k0 kn
  have lower := problem_window_nal_lower_bound n l h a a0 an k k0 kn
  have upper := problem_window_nal_upper_bound n l h a a0 an k k0 kn
  omega
