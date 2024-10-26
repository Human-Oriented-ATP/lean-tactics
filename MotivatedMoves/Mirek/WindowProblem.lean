import Mathlib.Tactic
import MotivatedMoves.Mirek.SmtSolver

def countWindow (l : List Bool) (x0 : ℕ) (x1 : ℕ) : ℕ
  := ((l.drop x0).take (x1-x0)).count true

theorem list_drop_drop (l : List Bool) (a b : ℕ)
: l.drop (a+b) = (l.drop a).drop b
:= by
  induction b
  · rfl
  · simp [add_comm]

theorem count_window_add (l : List Bool) (x0 x1 x2 : ℕ)
: x0 ≤ x1 → x1 ≤ x2
→ countWindow l x0 x1 + countWindow l x1 x2
  = countWindow l x0 x2
:= by
  intros h01 h12
  unfold countWindow
  rw [←List.count_append]
  apply congrArg
  have : x1 = (x1 - x0) + x0 := (Nat.sub_eq_iff_eq_add h01).mp rfl
  conv in (List.drop x1 l) => rw [this]
  rw [←List.drop_drop]
  set l2 := l.drop x0
  have : x2 - x0 = (x1 - x0) + (x2 - x1) := by omega
  rw [this]
  exact (List.take_add l2 (x1 - x0) (x2 - x1)).symm

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

theorem count_window_basic_bound (l : List Bool) (x0 : ℕ) (x1 : ℕ)
: x0 ≤ x1 → x0 + countWindow l x0 x1 ≤ x1
:= by
  intro h
  unfold countWindow
  have := List.count_le_length true ((l.drop x0).take (x1-x0))
  have := List.length_take_le (x1 - x0) (l.drop x0)
  omega

def problem_assump (n : ℕ) (l : List Bool) : Prop :=
  l.length = n^2 + n ∧
  ∀ k ≤ n^2-n,
    countWindow l k (k+n) < countWindow l (k+n) (k+2*n)

theorem problem_window_al_lower_bound (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ k ≤ n,
  countWindow l (n*k) (n*k + n) ≥ k
:= by
  intro ⟨h1,h2⟩
  intros k kh
  have := ineq_chain (λ x : ℕ ↦ countWindow l (n*x) (n*x + n)) 0 k (Nat.zero_le k) (by
    intros x _ _; simp [mul_add]
    have : n*x+n+n = n*x + 2*n := by omega
    rw [this]
    have := h2 (n*x)
    int_hammer
  )
  simp at this
  apply le_trans; swap; exact this
  apply Nat.le_add_left

theorem problem_window_al_upper_bound (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ k ≤ n,
  countWindow l (n*k) (n*k + n) ≤ k
:= by
  intros h k kh
  have from_chain := ineq_chain (λ x : ℕ ↦ countWindow l (n*x) (n*x + n)) k n kh (by
    intros x _ _; simp [mul_add]
    have : n*x+n+n = n*x + 2*n := by omega
    rw [this]
    apply h.2 (n*x)
    int_hammer
  )
  simp at from_chain
  have := count_window_basic_bound l (n * n) (n * n + n)
  int_hammer

theorem problem_window_al_value (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ k ≤ n,
  countWindow l (n*k) (n*k + n) = k
:= by
  intros h k kh
  apply Nat.le_antisymm
  apply problem_window_al_upper_bound n l h k kh
  apply problem_window_al_lower_bound n l h k kh

theorem problem_window_nal_lower_bound (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ a < n, ∀ k < n,
  countWindow l (n*k + a) (n*k + n + a) ≥ k
:= by
  intro ⟨h1, h2⟩
  intros a ah k kh
  have := ineq_chain (λ x : ℕ ↦ countWindow l (n*x+a) (n*x+a+n)) 0 k (Nat.zero_le k) (by
    intros x _ _
    simp
    have := h2 (n*x+a)
    have : n * (x+1) + a = n * x + a + n := by nlinarith
    rw [this]
    have : n * x + a + n + n = n * x + a + 2*n := by linarith
    rw [this]
    int_hammer
  )
  simp at this
  have : n * k + n + a = n * k + a + n := by linarith
  rw [this]
  omega

theorem problem_window_nal_upper_bound (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ a < n, ∀ k < n,
  countWindow l (n*k + a) (n*k + n + a) ≤ k+1
:= by
  intro ⟨h1,h2⟩
  intros a ah k kh
  have from_chain := ineq_chain (λ x : ℕ ↦ countWindow l (n*x+a) (n*x+a+n)) k (n-1) (
    Nat.le_sub_one_of_lt kh
  ) (by
    intros x _ _
    simp
    have := h2 (n*x+a)
    have := h2 (n*x+a)
    have : n * (x+1) + a = n * x + a + n := by nlinarith
    rw [this]
    have : n * x + a + n + n = n * x + a + 2*n := by linarith
    rw [this]
    int_hammer
  )
  have eq1 : n * (n - 1) + a + n = n * n + a := by int_hammer
  have eq2 : n * k + a + n = n * k + n + a := by linarith
  simp [eq1, eq2] at from_chain
  have := count_window_basic_bound l (n * (n-1) + a) (n*n + a)
  omega

theorem interval_cases (a b : ℕ)
: a ≤ b → b ≤ a+1 → b = a ∨ b = a+1
:= by intros; omega

theorem problem_window_nal_value (n : ℕ) (l : List Bool)
: problem_assump n l → ∀ a < n, ∀ k < n,
  countWindow l (n*k+a) (n*k+n+a) = k ∨ countWindow l (n*k+a) (n*k+n+a) = k+1
:= by
  intros h a ah k kh
  have lower := problem_window_nal_lower_bound n l h a ah k kh
  have upper := problem_window_nal_upper_bound n l h a ah k kh
  set a1 := countWindow l (n * k + a) n
  omega

theorem count_window_zero (l : List Bool) (a b : ℕ)
: b ≤ a → countWindow l a b = 0
:= by
  intro h
  unfold countWindow
  have : b - a = 0 := Nat.sub_eq_zero_of_le h
  simp [this]

theorem experiment1 (n : ℕ) (l : List Bool)
: problem_assump n l → n > 5 → countWindow l n (n+1) = 1 → False
:= by
  intros
  have h1 := problem_window_al_value n l (by assumption) 1 (by omega)
  simp [←Nat.two_mul] at h1
  have h2 : countWindow l (n+1) (2*n) = 0 := by
    have h2 := count_window_add l n (n+1) (2*n) (by omega) (by omega)
    omega
