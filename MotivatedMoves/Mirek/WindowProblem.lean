import Mathlib.Tactic
import MotivatedMoves.Mirek.SmtSolver

def countWindow (l : List Bool) (start : ℕ) (size : ℕ) : ℕ
  := ((l.drop start).take size).count true

#check List.drop_drop

theorem list_drop_drop (l : List Bool) (a b : ℕ)
: l.drop (a+b) = (l.drop a).drop b
:= by
  induction b
  · rfl
  · simp [add_comm]

theorem count_window_add (l : List Bool) (start a b : ℕ)
: countWindow l start a + countWindow l (start+a) b
  = countWindow l start (a+b)
:= by
  unfold countWindow
  rw [←List.count_append]
  apply congrArg
  rw [add_comm]
  rw [←List.drop_drop]
  set l2 := l.drop start
  exact (List.take_add l2 a b).symm

theorem ineq_chain_plus (f : ℕ → ℕ) (a b : ℕ)
: (∀ (n : ℕ), a ≤ n → n < a+b → f n < f (n+1))
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

#check Nat.sub_eq_iff_eq_add'
example (a b c : ℕ) (h1 : a ≤ b) (h2 : c = b-a) : b = a + c := by exact?

#check Nat.sub_eq_iff_eq_add'

theorem ineq_chain (f : ℕ → ℕ) (a b : ℕ)
: a ≤ b → (∀ (n : ℕ), a ≤ n → n < b → f n < f (n+1))
→ f b ≥ f a + (b-a)
:= by
  intros h1 h2
  set c := b-a
  have : b = a+c := (Nat.sub_eq_iff_eq_add' h1).mp rfl
  rw [this]
  rw [this] at h2
  exact ineq_chain_plus f a c h2

example (l : List Bool) : l.count true ≤ l.length := by exact List.count_le_length true l

theorem count_window_basic_bound (l : List Bool) (start : ℕ) (size : ℕ)
: countWindow l start size ≤ size
:= by
  unfold countWindow
  calc ((l.drop start).take size).count true ≤ ((l.drop start).take size).length := by apply List.count_le_length
    _ ≤ size := by apply List.length_take_le

def problem_assump (n : ℕ) (l : List Bool) : Prop :=
  l.length = n^2 + n ∧
  ∀ k ≤ n^2-n,
    countWindow l k n < countWindow l (k+n) n

theorem problem_window_al_lower_bound (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ k ≤ n,
  countWindow l (n*k) n ≥ k
:= by
  intros h k kh
  have := ineq_chain (λ x : ℕ ↦ countWindow l (n*x) n) 0 k (Nat.zero_le k) (by
    intros x _ _; simp [mul_add]
    apply h.2 (n*x)
    int_hammer
    -- have : n^2 - n = n*(n-1) := by
    --   simp [Nat.pow_two, Nat.mul_sub_left_distrib]
    -- rw [this]
    -- suffices : x ≤ n-1
    -- nlinarith
    -- omega
  )
  simp at this
  apply le_trans; swap; exact this
  apply Nat.le_add_left

theorem problem_window_al_upper_bound (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ k ≤ n,
  countWindow l (n*k) n ≤ k
:= by
  intros h k kh
  have from_chain := ineq_chain (λ x : ℕ ↦ countWindow l (n*x) n) k n kh (by
    intros x _ _; simp [mul_add]
    apply h.2 (n*x)
    int_hammer
    -- have : n^2 - n = n*(n-1) := by
    --   simp [Nat.pow_two, Nat.mul_sub_left_distrib]
    -- rw [this]
    -- suffices : x ≤ n-1
    -- nlinarith
    -- omega
  )
  simp at from_chain
  have basic_bound := count_window_basic_bound l (n * n) n
  have : k + (n - k) = n := Nat.add_sub_of_le kh
  linarith

theorem problem_window_al_value (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ k ≤ n,
  countWindow l (n*k) n = k
:= by
  intros h k kh
  apply Nat.le_antisymm
  apply problem_window_al_upper_bound n l h k kh
  apply problem_window_al_lower_bound n l h k kh

theorem problem_window_nal_lower_bound (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ a < n, ∀ k < n,
  countWindow l (n*k + a) n ≥ k
:= by
  intros h a ah k kh
  have := ineq_chain (λ x : ℕ ↦ countWindow l (n*x+a) n) 0 k (Nat.zero_le k) (by
    intros x _ _; simp [mul_add]
    rw [add_assoc, add_comm n a, ←add_assoc]
    apply h.2 (n*x+a)
    int_hammer
    -- have : n^2 - n = n*(n-1) := by
    --   simp [Nat.pow_two, Nat.mul_sub_left_distrib]
    -- rw [this]
    -- suffices : x < n-1
    -- nlinarith
    -- omega
  )
  simp at this
  apply le_trans; swap; exact this
  apply Nat.le_add_left

theorem problem_window_nal_upper_bound (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ a < n, ∀ k < n,
  countWindow l (n*k + a) n ≤ k+1
:= by
  intros h a ah k kh
  have from_chain := ineq_chain (λ x : ℕ ↦ countWindow l (n*x+a) n) k (n-1) (
    Nat.le_sub_one_of_lt kh
  ) (by
    intros x _ _; simp [mul_add]
    rw [add_assoc, add_comm n a, ←add_assoc]
    apply h.2 (n*x+a)
    -- int_hammer_show_smt
    int_hammer
    -- have : n^2 - n = n*(n-1) := by
    --   simp [Nat.pow_two, Nat.mul_sub_left_distrib]
    -- rw [this]
    -- nlinarith
  )
  simp at from_chain
  have basic_bound := count_window_basic_bound l (n * (n-1) + a) n
  omega

theorem interval_cases (a b : ℕ)
: a ≤ b → b ≤ a+1 → b = a ∨ b = a+1
:= by intros; omega

theorem problem_window_nal_value (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ a < n, ∀ k < n,
  countWindow l (n*k+a) n = k ∨ countWindow l (n*k+a) n = k+1
:= by
  intros h a ah k kh
  have lower := problem_window_nal_lower_bound n l h a ah k kh
  have upper := problem_window_nal_upper_bound n l h a ah k kh
  set a1 := countWindow l (n * k + a) n
  omega

theorem experiment1 (n : ℕ) (l : List Bool)
: problem_assump n l → n > 5 → countWindow l n 1 = 1 → False
:= by
  intros
  have h1 := problem_window_al_value n l (by assumption) 1 (by omega)
  simp at h1
  have h2 : countWindow l (n+1) (n-1) = 0 := by
    have h2 := count_window_add l n 1 (n-1)
    have s1 : 1+(n-1) = n := by omega
    simp [s1] at h2
    omega
