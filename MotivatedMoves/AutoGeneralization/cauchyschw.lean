import Lean
import Mathlib

open Lean Elab Tactic Meta Term Command
open BigOperators
-- theorem cauchy_schwartz_inequality_no_dp (n : ℕ) (u v : Fin n → ℝ) :
--   (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ i, v i ^ 2) :=
-- by
--   let P (x : ℝ) := ∑ i, (u i * x + v i) ^ 2
--   /- P is a polynomial which is always >= 0 -/
--   have each_term_in_P_nonneg : ∀ x i, 0 ≤ (u i * x + v i) ^ 2 := by
--     intro x i
--     apply sq_nonneg
--   have P_nonneg : ∀ x, 0 ≤ ∑ i, (u i * x + v i)^2 := by
--     intro x
--     apply Finset.sum_nonneg
--     simp at *
--     apply each_term_in_P_nonneg x
--   /- Rewrite P in the form Ax^2 + Bx + C -/
--   let A := ∑ i, (u i)^2
--   let B := 2 * ∑ i, u i * v i
--   let C := ∑ i, (v i)^2
--   def dotProduct (v w : Fin n → ℝ) : ℝ := ∑ i, v i * w i
--   have P_expr : ∀ x, P x = A * x^2 + B * x + C := by
--     intro x
--     dsimp
--   -- have := discrim_le_zero P_nonneg
--   sorry

def dp (v w : Fin n → ℝ) : ℝ := ∑ i, v i * w i
infix:70 " ⬝ " => dp

@[simps]
instance : HMul (Fin n → ℝ) ℝ (Fin n → ℝ) where
  hMul v s := fun i => v i * s

@[simps]
instance : HMul  ℝ (Fin n → ℝ) (Fin n → ℝ) where
  hMul s v := fun i => v i * s

/- Bilinearity Part 1 -/
theorem dp_distrib : ∀ a b c : Fin n → ℝ,
  (a+b) ⬝ (c) = (a ⬝ c + b ⬝ c) :=
by
  dsimp [dp]
  simp [← Finset.sum_add_distrib]
  intros a b c
  congr
  conv =>
    lhs
    intro i
    rw [add_mul]

/- Bilinearity Part 2 -/
theorem dp_scal : ∀ (v w : Fin n → ℝ) (s : ℝ),
  ((v*s) ⬝ w) = (v ⬝ w)*s :=
by
  dsimp [dp];
  intro v w s
  rw [Finset.sum_mul]
  congr
  conv =>
    lhs
    intro i
    rw [mul_assoc]
    rw [mul_comm s (w i)]
    rw [← mul_assoc]


/- Symmetry -/
theorem dp_symm : ∀ a b : Fin n → ℝ,
  a ⬝ b = b ⬝ a := by {dsimp [dp]; simp [mul_comm]}

theorem cauchy_schwartz_inequality (n : ℕ) (u v : Fin n → ℝ) :
  (u ⬝ v) ^ 2 ≤ (u ⬝ u) * (v ⬝ v) :=
by
  let P (x : ℝ) := (u * x + v) ⬝ (u * x + v)

  /- P is a polynomial which is always >= 0... i.e. pos semi-definiteness-/
  have P_nonneg : ∀ x, 0 ≤ P x:= by
    intro x
    dsimp
    rw [dp]
    ring_nf
    apply Finset.sum_nonneg
    intro i hi
    apply sq_nonneg

  /- Rewrite P in the form Ax^2 + Bx + C -/
  let A := u ⬝ u
  let B := 2 * (u ⬝ v)
  let C := v ⬝ v

  have P_alt : ∀ x, P x = A * x * x + B * x + C := by
    intro x
    dsimp

    rw [dp_distrib]
    rw [dp_symm]
    rw [dp_distrib]

    nth_rewrite 3 [dp_symm]
    rw [dp_distrib]
    nth_rewrite 3 [dp_symm]
    ring_nf

    rw [dp_scal]
    rw [dp_symm]
    rw [dp_scal]
    ring_nf

    nth_rewrite 2 [dp_symm]
    rw [dp_scal]
    ring_nf

  have P_nonneg_alt : ∀ (x : ℝ), 0 ≤ A * x * x + B * x + C := by
    intro x
    rw [← P_alt x]
    exact P_nonneg x
  clear P_nonneg
  clear P_alt

  have d_leq_zero := discrim_le_zero P_nonneg_alt
  dsimp [discrim] at d_leq_zero
  ring_nf at d_leq_zero
  simp at d_leq_zero
  assumption
