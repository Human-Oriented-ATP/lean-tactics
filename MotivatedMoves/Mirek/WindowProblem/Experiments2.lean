import MotivatedMoves.Mirek.WindowProblem.Defs
import MotivatedMoves.Mirek.WindowProblem.Tactics

theorem aux1 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 4 → countWindow l n (n+1) = 0
:= by
  intros
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h 0 (by omega) (by omega)
  have := problem_window_al_value n l h 1 (by omega) (by omega)
  have := problem_window_nal_value n l h 1 (by omega) 1 (by omega) (by omega)
  have := window_ineq 1 (by omega)
  ring_nf at *
  window_tactic

theorem aux2 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 4 → countWindow l (2*n) (2*n+1) = 0
:= by
  intros
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h 0 (by omega) (by omega)
  have := problem_window_al_value n l h 1 (by omega) (by omega)
  have := aux1 n l h
  have := window_ineq (n+1) (by omega)
  have := problem_window_al_value n l h 2 (by omega) (by omega)
  ring_nf at *
  window_tactic

theorem aux3 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 4 → countWindow l (n+1) (n+2) = 0
:= by
  intros
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h 0 (by omega) (by omega)
  have := aux1 n l h
  --have := problem_window_nal_value n l h 1 (by omega) 1 (by omega) (by omega)
  have := problem_window_al_value n l h 1 (by omega) (by omega)
  have := problem_window_nal_value n l h 1 (by omega) 2 (by omega) (by omega)
  have := window_ineq 2 (by omega)
  have := aux2 n l h
  ring_nf at *
  window_tactic

theorem aux4 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 4 → countWindow l (3*n) (3*n+1) = 0
:= by
  intros
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h 2 (by omega) (by omega)
  have := aux2 n l h
  have := problem_window_nal_value n l h 2 (by omega) 1 (by omega) (by omega)
  have := window_ineq (2*n+1) (by omega)
  have := problem_window_al_value n l h 3 (by omega) (by omega)
  ring_nf at *
  window_tactic

theorem aux5' (n : ℤ) (l : List Bool) (h : problem_assump n l) (j : ℕ) (h2 : j ≤ n-1) (h3 : j ≥ 0)
: n ≥ 4 → countWindow l (j*n) (j*n+1) = 0
:= by
  intros
  let ⟨h1,h2,window_ineq⟩ := h
  match j with
  | 0 =>
    have := problem_window_al_value n l h 0 (by omega) (by omega)
    window_tactic
  | j + 1 =>
    have := aux5' n l h j (by omega) (by omega) (by omega)
    have := problem_window_al_value n l h j (by omega) (by omega)
    have := problem_window_nal_value n l h j (by omega) 1 (by omega) (by omega)
    have : j*n ≥ 0 := by refine Int.mul_nonneg (by omega) (by omega)
    have := window_ineq (j*n+1) (by omega)
    have := problem_window_al_value n l h (j+1) (by omega) (by omega)
    ring_nf at *
    window_tactic

theorem aux5 (n : ℤ) (l : List Bool) (h : problem_assump n l) (j : ℤ) (h2 : j ≤ n-1) (h3 : j ≥ 0)
: n ≥ 4 → countWindow l (j*n) (j*n+1) = 0 :=
by
  have aux := aux5' n l h (j.toNat) (by omega) (by omega)
  have := Int.toNat_of_nonneg h3
  rw [this] at aux;assumption

#check Int.toNat

theorem problem_window_nal_high (n : ℤ) (l : List Bool) (h : problem_assump n l)  (j k : ℤ)
 (pos : j ≥ 0) (lt_n : k < n) (hjk : j ≤ k) (ha1 : a ≥ 0) (ha2 : a < n)
: (countWindow l (n*j + a) (n*j+n+a) = j+1) → (countWindow l (n*k + a) (n*k+n+a) = k+1) :=
by
  intros h''
  let ⟨h1,h2,window_ineq⟩ := h
  have aux := problem_window_nal_value n l h a (by omega) k (by omega) (by omega)
  have := ineq_chain (λ x : ℤ ↦ countWindow l (n*x + a) (n*x + n + a)) j k (by omega) (by
    intros x _ _; simp
    have ineq := window_ineq (n * x + a)
    ring_nf at *
    int_hammer
  )
  simp at this; omega


theorem problem_window_nal_low (n : ℤ) (l : List Bool) (h : problem_assump n l) (j k a: ℤ) (hjk : j ≤ k)
(pos : j ≥ 0) (lt_n : k < n) (hjk : j ≤ k) (ha1 : a ≥ 0) (ha2 : a < n)
: (countWindow l (n*k + a) (n*k+n+a) = k) → (countWindow l (n*j + a) (n*j+n+a) = j) :=
by
  intro
  have := problem_window_nal_high n l h j k pos lt_n hjk ha1 ha2
  have aux := problem_window_nal_value n l h a (by omega) j (by omega) (by omega)
  cases aux <;> omega

theorem aux6 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 4 → countWindow l ((n-2)*n + 1) ((n-1)*n+1) = n-2
:= by
  intros
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h (n-2) (by omega) (by omega)
  have := aux5 n l h (n-2) (by omega) (by omega) (by omega)
  have := aux5 n l h (n-1) (by omega) (by omega) (by omega)
  ring_nf at *
  window_tactic

theorem aux7 (n : ℤ) (l : List Bool) (h : problem_assump n l) (j : ℤ) (nj : 0 ≤ j) (hj : j ≤ n - 2)
: n ≥ 4 → countWindow l (n*j + 1) (n*j+n+1) = j
:= by
  intros
  let ⟨h1,h2,window_ineq⟩ := h
  have := aux6 n l h
  have := problem_window_nal_low n l h j (n-2) 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  ring_nf at *
  window_tactic


theorem aux8' (n : ℤ) (l : List Bool) (h : problem_assump n l) (j : ℕ) (a : ℕ) (h1 : a ≤ n)
(h2 : j ≤ n-a-1) (h3 : j ≥ 0)
(h4 : (k : ℤ) → (k ≥ 0) → (k ≤ n-a-1) → countWindow l (n*k+a) (n*k+n+a) = k)
: n ≥ 4 → countWindow l (n*j) (n*j+a+1) = 0
:= by
  intros
  let ⟨h1,h2,window_ineq⟩ := h
  match j, a with
  | 0, _ =>
    have := problem_window_al_value n l h 0 (by omega) (by omega)
    window_tactic
  | j + 1, 0 =>
    have := aux5' n l h (j+1) (by omega) (by omega) (by omega)
    window_tactic
  | j + 1, a + 1 =>
    have := aux8' n l h j (a+1) (by omega) (by omega) (by omega) (by
      intros k _ _;have := h4 k (by omega) (by omega);omega) (by omega)
    have := h4 j (by omega) (by omega)
    have := h4 (j+1) (by omega) (by omega)
    have := problem_window_al_value n l h j (by omega) (by omega)
    have := problem_window_al_value n l h (j+1) (by omega) (by omega)
    have : j*n ≥ 0 := by refine Int.mul_nonneg (by omega) (by omega)
    have := window_ineq (j*n+a+2) (by omega)
    simp at *
    ring_nf at *
    window_tactic

theorem aux8 (n : ℤ) (l : List Bool) (h : problem_assump n l) (j : ℤ) (a : ℤ) (h1: a ≤ n)
(h2 : j ≤ n-a-1) (h3 : j ≥ 0) (h3' : a ≥ 0)
(h4 : (k : ℤ) → (k ≥ 0) → (k ≤ n-a-1) → countWindow l (n*k+a) (n*k+n+a) = k)
: n ≥ 4 → countWindow l (n*j) (n*j+a+1) = 0
:=by
  intros
  have aux := aux8' n l h (j.toNat) (a.toNat) (by omega) (by omega) (by omega) (by aesop) (by omega)
  aesop



theorem aux9' (n : ℤ) (l : List Bool) (h : problem_assump n l) (a : ℤ) (h1 : a ≤ n-2) (h2 : a ≥ 0)
(h4 : (k : ℤ) → (k ≥ 0) → (k ≤ n-a-1) → countWindow l (n*k+a) (n*k+n+a) = k)
(h5 : countWindow l (n*(n-a-1) + a) (n*(n-a) + a) = n-a-1)
: n ≥ 4 → countWindow l (n*(n-a-2) + a+1) (n*(n-a-1) + a+1) = n-a-2
:= by
  intros
  let ⟨h1',h2',window_ineq⟩ := h
  have := problem_window_al_value n l h (n-a-1) (by omega) (by omega)
  have := problem_window_al_value n l h (n-a-2) (by omega) (by omega)
  have := aux8 n l h (n-a-1) a (by omega) (by omega) (by omega) (by omega) (by aesop) (by omega)
  have := aux8 n l h (n-a-2) a (by omega) (by omega) (by omega) (by omega) (by aesop) (by omega)
  simp at *
  ring_nf at *
  window_tactic


theorem aux10' (n : ℤ) (l : List Bool) (h : problem_assump n l) (a : ℤ) (h1 : a ≤ n-2) (h2 : a ≥ 1)
(h4 : (k : ℤ) → (k ≥ 0) → (k ≤ n-a-1) → countWindow l (n*k+a) (n*k+n+a) = k)
(h5 : countWindow l (n*(n-a-1) + a) (n*(n-a) + a) = n-a-1)
(j : ℤ) (nj : 0 ≤ j) (hj : j ≤ n - a - 2)
: n ≥ 4 → countWindow l (n*j + (a+1)) (n*j + n + (a+1)) = j
:= by
  intros
  let ⟨h1',h2',window_ineq⟩ := h
  have := aux9' n l h a (by omega) (by omega) (by aesop) (by omega) (by omega)
  have := problem_window_nal_low n l h j (n-a-2) (a+1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  ring_nf at *
  window_tactic

theorem aux11' (n : ℤ) (l : List Bool) (h : problem_assump n l) (a : ℤ) (h1 : a ≤ n-2) (h2 : a ≥ 0)
(k : ℤ) (kp: k ≥ 0) (kb: k ≤ n-a-1):
n ≥ 4 → countWindow l (n*k+a) (n*k+n+a) = k
:= by
  intros
  by_cases ha : a ≥ 2
  case neg =>
    by_cases ha' : a ≥ 1
    case pos =>
      have := problem_window_al_value n l h k (by omega) (by omega)
      have := aux5 n l h k (by omega) (by omega) (by omega)
      have := aux5 n l h (k+1) (by omega) (by omega) (by omega)
      window_tactic
    case neg =>
      have := problem_window_al_value n l h k (by omega) (by omega)
      window_tactic
  case pos =>
    have aux := aux11' n l h (a-1) (by omega) (by omega) --k (by omega) (by omega) (by omega)
    have := aux8 n l h (n-(a)) (a-1) (by omega) (by omega) (by omega) (by omega) (by aesop) (by omega)
    have := aux10' n l h (a-1) (by omega) (by omega) (by aesop) (by
      have := aux (n-a) (by omega) (by omega) (by omega)
      ring_nf at *
      window_tactic
    ) k (by aesop) (by omega) (by omega)
    window_tactic

termination_by a.toNat

theorem aux12 (n : ℤ) (l : List Bool) (h : problem_assump n l) (j : ℤ)
(h2 : j ≤ n-1) (h3 : j ≥ 0)
: n ≥ 4 → countWindow l (n*j) (n*j+(n-j)) = 0
:=by
  intros
  by_cases j ≥ 1
  case pos =>
    have := aux8 n l h j (n-j-1) (by omega) (by omega) (by omega) (by omega) (by
      have := aux11' n l h (n-j-1) (by omega) (by omega); aesop)
    ring_nf at *
    aesop
  case neg =>
    have := problem_window_al_value n l h 0 (by omega) (by omega)
    ring_nf at *
    window_tactic

theorem aux13 (n : ℤ) (l : List Bool) (h : problem_assump n l) (j : ℤ)
(h2 : j ≤ n) (h3 : j ≥ 0)
: n ≥ 4 → countWindow l (n*j + (n-j)) (n*j+n) = j
:=by
  intros
  by_cases ha : j ≤ n - 1
  case pos =>
    have := aux12 n l h j (by omega) (by omega) (by omega)
    have := problem_window_al_value n l h j (by omega) (by omega)
    window_tactic
  case neg =>
    have := problem_window_al_value n l h n (by omega) (by omega)
    ring_nf at *
    window_tactic
