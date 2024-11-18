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
: n ≥ 4 → countWindow l (n+1) (n+2) = 0
:= by
  intro hn
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h 0 (by omega) (by omega)
  have := problem_window_al_value n l h 1 (by omega) (by omega)
  have := aux1 n l h hn
  have := problem_window_nal_value n l h 1 (by omega) 1 (by omega) (by omega)
  have := window_ineq 2 (by omega)
  have := problem_window_al_value n l h 2 (by omega) (by omega)
  have := window_ineq (n+2) (by omega)
  ring_nf at *
  window_tactic

theorem aux3 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 4 → countWindow l (n+2) (n+3) = 0
:= by
  intro hn
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h 0 (by omega) (by omega)
  have := problem_window_al_value n l h 1 (by omega) (by omega)
  have := problem_window_al_value n l h 2 (by omega) (by omega)
  have := window_ineq 3 (by omega)
  have := window_ineq (n+3) (by omega) (by nlinarith)
  have := window_ineq (2*n+3) (by omega) (by nlinarith)
  have := problem_window_al_value n l h 3 (by omega) (by omega)
  ring_nf at *
  window_tactic

theorem aux4 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n = 4 → countWindow l (n+3) (n+4) = 1
:= by
  intro hn
  let ⟨h1,h2,window_ineq⟩ := h
  have := aux1 n l h (by omega)
  have := aux2 n l h (by omega)
  have := aux3 n l h (by omega)
  have := problem_window_al_value n l h 1 (by omega) (by omega)
  ring_nf at *
  window_tactic

theorem aux5 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 5 → countWindow l (n+3) (n+4) = 0
:= by
  intro hn
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h 1 (by omega) (by omega)
  have := window_ineq 4 (by omega)
  have := problem_window_al_value n l h 2 (by omega) (by omega)
  have := window_ineq (n+4) (by omega)
  have := problem_window_al_value n l h 3 (by omega) (by omega)
  have := window_ineq (2*n+4) (by omega)
  have := problem_window_al_value n l h 4 (by omega) (by omega)
  have := window_ineq (3*n+4) (by omega)
  ring_nf at *
  window_tactic

example (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 6 → countWindow l (n+4) (n+5) = 0
:= by
  intro hn
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h 1 (by omega) (by omega)
  have := window_ineq 5 (by omega)
  have := problem_window_al_value n l h 2 (by omega) (by omega)
  ring_nf at *
  window_tactic
  sorry

theorem aux6 (n k a : ℤ) (l : List Bool) (h : problem_assump n l)
: k > 0 → k < n → a > 0 → a < n →
  countWindow l (n*k) (n*k+a) = k → countWindow l (n*(k+1)) (n*(k+1)+a) = k+1
:= by
  intros h0 hn ha0 han hPrev
  let ⟨h1,h2,window_ineq⟩ := h
  have := problem_window_al_value n l h k (by omega) (by omega)
  have := window_ineq (n*(k-1)+a) (by nlinarith)
  have := problem_window_al_value n l h (k+1) (by omega) (by omega)
  ring_nf at *
  window_tactic

theorem aux7 (n k a : ℤ) (l : List Bool) (h : problem_assump n l)
: a > 0 → a < n → countWindow l n (n+a) = 1 →
  k > 0 → k ≤ n → countWindow l (n*k) (n*k+a) = k
:= by
  intros ha0 han hi0 hk0
  have : (k-1) = (k-1).toNat := Eq.symm (Int.toNat_sub_of_le hk0)
  have : k = (k-1).toNat+1 := by omega
  rw [this]
  induction (k-1).toNat with
  | zero =>
    simp [hi0]
  | succ k ih =>
    intro hkn
    have := (
      aux6 n (↑k + 1) a l h
      (Int.succ_ofNat_pos k)
      hkn ha0 han
      (by exact (ih (Int.le_of_lt hkn)))
    )
    simp [this]

theorem aux8 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n > 0 → countWindow l n (2*n-1) = 0
:= by
  intro h0
  let ⟨h1,h2,window_ineq⟩ := h
  by_contra
  have : countWindow l n (n + (n-1)) = 1 := by
    have := problem_window_al_value n l h 1 Int.one_nonneg h0
    window_tactic
  by_cases hc : n = 1
  · rw [hc] at this
    simp at this
    window_tactic
  · have := (
      aux7 n n (n-1) l h
      (by omega) (sub_one_lt n) this
      (by omega) (Int.le_refl n)
    )
    window_tactic

theorem aux9 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n > 0 → countWindow l (2*n-1) (2*n) = 1
:= by
  intro h0
  have := aux8 n l h h0
  have := problem_window_al_value n l h 1 Int.one_nonneg h0
  window_tactic

theorem aux10 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 5 → countWindow l (2*n) (2*n+1) = 0
:= by
  intro hn
  let ⟨h1,h2,window_ineq⟩ := h
  have := aux8 n l h (by omega)
  have := aux9 n l h (by omega)
  have := problem_window_nal_value n l h
    (n-1) ⟨by omega, sub_one_lt n⟩ 1 (by omega) (by omega)
  have := window_ineq (n+1) (by omega)
  ring_nf at *
  window_tactic

example (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 5 → countWindow l (2*n+1) (2*n+2) = 0
:= by
  intro hn
  let ⟨h1,h2,window_ineq⟩ := h
  have := aux8 n l h (by omega)
  have := aux9 n l h (by omega)
  have := aux10 n l h (by omega)
  have := problem_window_al_value n l h 2 (by omega) (by omega)
  have := window_ineq (n+2) (by omega)
  have := window_ineq (2*n-1) (by omega)
  have := problem_window_al_value n l h 3 (by omega) (by omega)
  sorry

theorem aux11 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 5 → countWindow l (3*n-1) (3*n) = 1
:= by
  intro hn
  let ⟨h1,h2,window_ineq⟩ := h
  have := aux8 n l h (by omega)
  have := aux9 n l h (by omega)
  have := problem_window_al_value n l h 2 (by omega) (by omega)
  have := problem_window_nal_value n l h
    (n-1) (by omega) 1 (by omega) (by omega)
  ring_nf at *
  window_tactic

theorem aux12 (n : ℤ) (l : List Bool) (h : problem_assump n l)
: n ≥ 5 → countWindow l (4*n-1) (4*n) = 1
:= by
  intro hn
  let ⟨h1,h2,window_ineq⟩ := h
  have := aux11 n l h (by omega)
  have := problem_window_al_value n l h 3 (by omega) (by omega)
  have := problem_window_nal_value n l h
    (n-1) (by omega) 2 (by omega) (by omega)
  ring_nf at *
  window_tactic

theorem aux13 (n k : ℤ) (l : List Bool) (h : problem_assump n l)
: k ≥ 2 → k ≤ n+1 → countWindow l (k*n-1) (k*n) = 1
:= by
  intro hk0
  have : (k-2) = (k-2).toNat := Eq.symm (Int.toNat_sub_of_le hk0)
  have : k = (k-2).toNat+2 := by omega
  rw [this]
  induction (k-2).toNat with
  | zero =>
    simp
    intro hn1
    exact aux9 n l h (by omega)
  | succ k ih =>
    simp
    intro hkn
    have := problem_window_al_value n l h (↑k+2) (by omega) (by omega)
    have := problem_window_nal_value n l h (n-1) (by omega) (↑k+1) (by omega) (by omega)
    ring_nf at *
    window_tactic
