/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Proof-based generalization.
Accounts for constants playing the same role in different places.
Accounts for generalizing constants to functions.
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/

import MotivatedMoves.AutoGeneralization.AutoGeneralizeTactic

import MotivatedMoves.AutoGeneralization.Formalizations.hcf_algorithm
import MotivatedMoves.AutoGeneralization.Formalizations.irrationality_of_sqrts
import MotivatedMoves.AutoGeneralization.Formalizations.non_multiples_of_k
import MotivatedMoves.AutoGeneralization.Formalizations.impossible_graphs

open Autogeneralize

open Real
open Lean Elab Tactic Meta Term Command

set_option linter.unusedVariables false
set_option pp.showLetValues false
-- set_option  false
-- set_option pp.explicit true
-- set_option profiler true
-- set_option trace.Meta.whnf true
set_option trace.TypecheckingErrors true
set_option trace.ProofPrinting true

-- #check AbstractMVars.State.abstractLevels
example :  1 + 2 = 2 + 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n := Nat.mul_comm
  -- autogeneralize_basic ℕ  in mult_comm
  autogeneralize_basic (Mul.mul.{0} (α := ℕ)) in mult_comm
  specialize mult_comm.Gen Add.add Nat.add_comm 1 2
  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GCD ALGORITHM
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

-- #print Int.hcf
-- #print Int.hcf._unary
example : True := by
  autogeneralize ℤ in hcf._unary
  specialize hcf._unary.Gen ℂ
  trivial

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING PROOFS OF GRAPH DEGREE SEQUENCE
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example :
  ∀ (G : SimpleGraph (Fin 5)) [inst : DecidableRel G.Adj],
  (∃ v, G.degree v = 1 ∧ ∀ (w : Fin 5), w ≠ v → G.degree w = 4) → False
:= by
  autogeneralize (4:ℕ) in impossible_graph -- gen 4 first doesn't work b/c comp rule

  specialize impossible_graph.Gen 5
  apply impossible_graph.Gen (by trivial)




example : ∀ (G : SimpleGraph (Fin 5)) [inst : DecidableRel G.Adj],
  (∃ v, G.degree v = 1 ∧ ∀ (w : Fin 5), w ≠ v → G.degree w = 4) → False
:= by
  autogeneralize (3:ℕ) in impossible_graph
  autogeneralize (4:ℕ) in impossible_graph.Gen

  specialize impossible_graph.Gen.Gen 5
  apply impossible_graph.Gen.Gen (by trivial)

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
PRODUCT OF NONEVENS IS NONEVEN
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

lemma ndvd_to_mod {n : ℕ} : 2 ∤ n ↔ n % 2 = 1 := Nat.two_dvd_ne_zero

-- lemma ndvd_to_mod' {d n : ℕ} : d ∤ n ↔ d % n ≠ 0 := by
--   constructor
--   sorry

-- with inline definitions of odd
lemma product_of_nonmultiplesoftwo (m n : Nat) :
  (2 ∤ m) ∧  (2 ∤ n) → (2 ∤ m*n) :=
by
  -- repeat rw [ndiv]
  repeat rw [ndvd_to_mod] -- so they are all 1 mod 2
  repeat rw [mod_means_exists_k] at *
  rintro ⟨⟨kₘ, m_odd⟩, ⟨kₙ, n_odd⟩⟩

  use (kₘ*2*kₙ + kₘ + kₙ)
  rw [← m_odd, ← n_odd]
  rewrite [add_mul,mul_add, mul_add, mul_add, mul_add, mul_one, mul_one, one_mul]
  rewrite [mul_assoc, mul_assoc, add_assoc,add_assoc]
  rfl

  repeat exact Nat.one_lt_two

example : True := by
  have product_of_nonmultiplesoftwo := product_of_nonmultiplesoftwo
  autogeneralize (2:ℕ) in product_of_nonmultiplesoftwo
  specialize product_of_nonmultiplesoftwo.Gen 3 3
  trivial

-- lemma product_of_nonmultiplesofthree (m n : Nat) :
--   (3 ∤ m) ∧  (3 ∤ n) → (3 ∤ m*n) :=
-- by
--   repeat rw [ndvd_to_mod'] -- so they are all 1 mod 2
--   repeat rw [mod_means_exists_k'] at *
--   simp
--   intros h1 h2 k
--   sorry


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
PRODUCT OF ODDS IS ODD
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
lemma product_of_odds'  : ∀ a b : ℕ, Odd ((2*a+1)*(2*b+1)):= by
  intros a b
  use (a*2*b + a + b)
  rewrite [add_mul,mul_add, mul_add, mul_add, mul_add, mul_one, mul_one, one_mul]
  rewrite [mul_assoc, mul_assoc, add_assoc,add_assoc,add_assoc]
  rfl

example : ∀ (a b : ℕ), ∃ k, (3 * a + 1) * (3 * b + 1) = 3 * k + 1 := by
  have product_of_odds' := product_of_odds'
  autogeneralize (2:ℕ) in product_of_odds'
  specialize product_of_odds'.Gen 3
  assumption


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
PRODUCT OF ODDS IS ODD -- with custom definition of odd
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

lemma product_of_odds (m n : Nat) :
    have odd := fun (n : Nat) ↦ ∃ k : Nat, n = 2 * k + 1;
    odd m ∧ odd n → odd (m * n) := by
  dsimp
  rintro ⟨⟨a,m_odd⟩ , ⟨b,n_odd⟩⟩
  rw [m_odd]
  rw [n_odd]
  use (a*2*b + a + b)
  rewrite [add_mul,mul_add, mul_add, mul_add, mul_add, mul_one, mul_one, one_mul]
  rewrite [mul_assoc, mul_assoc, add_assoc,add_assoc,add_assoc]
  rfl

example : True := by
  have product_of_odds := product_of_odds
  autogeneralize (2:ℕ) in product_of_odds -- now the definition is inside the proof, so it works.
  -- need to modify tactic to see the "2" within the definition of "odd"
  -- autogeneralize_basic (2:ℕ) in product_of_odds

  trivial


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
FOUR IS THE SUM OF TWO ODDS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
def four_is_sum_of_odds : ∃ m n : ℕ, Odd m ∧ Odd n ∧ m+n=4 := by
  use 3
  use 1
  constructor
  exact Nat.odd_iff.mpr rfl
  constructor
  -- simp only [odd_one]
  exact Nat.odd_iff.mpr rfl
  simp only [Nat.reduceAdd]

example : True := by
  have four_is_sum_of_odds := four_is_sum_of_odds
  autogeneralize 4 in four_is_sum_of_odds -- exist 2 odds which sum to 3 + 1
  -- autogeneralize 3 in four_is_sum_of_odds.Gen
  -- simp at four_is_sum_of_odds.Gen.Gen
  -- specialize four_is_sum_of_odds.Gen.Gen 7
  -- dsimp at four_is_sum_of_odds.Gen.Gen
  trivial





/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING PROOFS OF SET SUMS - WITHOUT USING A LEMMA IN GENERALITY
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
-- variable (α : Type) [inst : Fintype α] [inst_2 : DecidableEq α]

-- omit inst in
theorem union_of_finsets (α : Type) [inst : Fintype α] [inst_2 : DecidableEq α] (A B : Finset α) (hA : A.card = 2) (hB : B.card = 2) : (A ∪ B).card ≤ 4 := by
    apply hA ▸ hB ▸ Finset.card_union_add_card_inter A B ▸ Nat.le_add_right _ _

#print union_of_finsets

-- in 2 steps
example : ∀ (α : Type) [inst : Fintype α] [inst_2 : DecidableEq α] (A B : Finset α), A.card = 3 → B.card = 4 → (A ∪ B).card ≤ 7:= by
  -- autogeneralize_basic (2:ℕ) in union_of_finsets -- Pons fails, as expected
  autogeneralize (4:ℕ) in union_of_finsets
  autogeneralize (2:ℕ) in union_of_finsets.Gen
  specialize union_of_finsets.Gen.Gen 3 4
  assumption

-- in 1 step
example : ∀ (α : Type) [inst : Fintype α] [inst_2 : DecidableEq α] (A B : Finset α), A.card = 3 → B.card = 4 → (A ∪ B).card ≤ 7:= by
  -- autogeneralize_basic (2:ℕ) in union_of_finsets -- Pons fails, as expected
  -- autogeneralize (4:ℕ) in union_of_finsets

  autogeneralize (2:ℕ) in union_of_finsets
  specialize union_of_finsets.Gen 3 4
  assumption


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
DIVISIBILITY RULE
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
-- theorem div_rule : ∀ p: ℕ, Prime p ∧ p > 3 → 2 * p ∣ (4*(4^(p-1) - 1)/3) := by
--   intro p ⟨pprime, pgeq3⟩

--   -- simp?
--   -- linarith
--   -- aesop
--   sorry


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
X+X IS EVEN
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
theorem x_plus_x_is_even : ∀ x: ℕ, Even (x+x) := by
  -- exact? -- closes the goal
  aesop -- also closes teh goal


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
DEPENDING ON X≠0 and not
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--
Fabian's example:
  "hyp" is a proof that DOES NOT depend on the fact that x ≠ 0 to prove P  (even though x ≠ 0 is proven at some point on the proof)
  and therefore generalizes to
  "hyp.Gen" which is a proof that ∀ x, P x
-/
def P (x : ℝ) := ∀ y : ℝ, y = 0 → x * y = 0 -- if y is zero, so is y multiplied by anything else
example : ∀ x : ℝ, P x := by
  let hyp :  ∀ y : ℝ, y = 0 → 2 * y = 0 := by {intro y h; have twoneq : (2:ℝ) ≠ 0 := two_ne_zero; apply mul_eq_zero_of_right; apply h};
  autogeneralize (2:ℝ) in hyp -- generalizes to a statement that works for all x:ℝ, not requiring x ≠ 0
  assumption

/--
Fabian's example:
  "hyp" is a proof that DOES depend on the fact that x ≠ 0 to prove P
  and therefore generalizes to
  "hyp.Gen" which is a proof that ∀ x, x ≠ 0 → P x
-/
def P' (x : ℕ) := ∀ y : ℕ, x * y = 0 → y = 0 -- if the product if x and y is 0, then y is zero
-- example : ∀ x : ℕ, x ≠ 0 → P' x := by
--   let hyp :  ∀ y : ℕ, 3 * y = 0 → y = 0 := by {intro y h;  let twoneq : (3:ℕ) ≠ 0 := Ne.symm (Nat.zero_ne_add_one 2); apply eq_zero_of_ne_zero_of_mul_left_eq_zero twoneq h; };
--   autogeneralize (3:ℕ) in hyp
--   -- autogeneralize (3:ℕ) in hyp.Gen
--   -- autogeneralize ((1+2):ℕ) in hyp.Gen.Gen
--   assumption -- throws error; needs proofs with holes


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING PROOFS OF IRRATIONALITY.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--To screenshot-/

example := by
  let irrat_sqrt : Irrational (sqrt 2) := by {apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize (2:ℕ) in irrat_sqrt




  use 1
/--
Example:
sqrt(2) is irrational generalizes to sqrt(prime) is irrational
-/
example : Irrational (sqrt 3) := by
  let sum_irrat : Irrational (sqrt (2:ℕ)) := by {apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize_basic (2:ℕ) in sum_irrat
  specialize sum_irrat.Gen 3 (Nat.prime_three)
  assumption

/--
Example of a naive, over-specialized generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+prime is irrational
-/
example : Irrational (sqrt 3 + 3) := by
  let sum_irrat : Irrational (sqrt (2:ℕ) + 2) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize_basic (2:ℕ) in sum_irrat
  specialize sum_irrat.Gen 3 (Nat.prime_three)
  assumption

/--
Example of a better, constant-aware generalization:
sqrt(2)+2 is irrational generalizes to sqrt(prime)+nat is irrational
-/
example : Irrational (sqrt 3 + 6) := by
  let sum_irrat : Irrational (sqrt (2:ℕ) + 2) := by {apply Irrational.add_nat; apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 2 ∣ a := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 2 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 2 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 2 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 2] at h; have := Nat.Prime.ne_zero Nat.prime_two; cases h with | inl => have b_div : 2 ∣ b := by {have c := (Nat.Prime.dvd_mul (Nat.prime_two)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 2 ∣ gcd a b := by {apply Iff.mpr (dvd_gcd_iff _ _ _) ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (Nat.prime_two) p_dvd_gcd | inr => apply this; assumption}
  autogeneralize (2:ℕ) in sum_irrat
  specialize sum_irrat.Gen 3 (Nat.prime_three) 6
  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING SIZES OF SETS.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

variable {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α]
/--
Example to screenshot
-/

example :=
by
  let fun_set :
    Fintype.card α = 3 → Fintype.card β = 3 →
    Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}

  autogeneralize 3 in fun_set








  use 1

/--
Example of a naive, over-specialized generalization:
This generalizes all four 3s in the same way. (There are four 3s in the theorem statement.  2 are related, 2 not.)
-/
example : Fintype.card α = 4 → Fintype.card β = 4 → Fintype.card (α → β) = 4 ^ 4 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize_basic 3 in fun_set
  specialize @fun_set.Gen 4
  assumption

/--
Example of a better, constant-aware generalization:
Generalizes the pairs of 3s separately.
-/
example : Fintype.card α = 4 → Fintype.card β = 5 → Fintype.card (α → β) = 5 ^ 4 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize 3 in fun_set
  specialize @fun_set.Gen 4 5
  assumption

/--
Demonstration of functionality to generalize at specified occurrences.
This generalizes just the first pair of 3s.
-/
example : Fintype.card α = 4 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 4 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize 3 in fun_set at occurrences [1]
  specialize @fun_set.Gen 4
  assumption

/--
Demonstration of functionality to generalize at specified occurrences.
This generalizes just the second pair of 3s.
-/
example : Fintype.card α = 3 → Fintype.card β = 4 → Fintype.card (α → β) = 4 ^ 3 :=
by
  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}
  autogeneralize 3 in fun_set at occurrences [2]
  specialize @fun_set.Gen 4
  assumption


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING FUNCTIONS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--
Generalizing an operator that only requires commutativity.
-/

example :  1 + 2 = 2 + 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm
  autogeneralize_basic (Mul.mul (α := ℕ)) in mult_comm -- generalize all
  specialize mult_comm.Gen Add.add Nat.add_comm 1 2
  assumption

example :  1 + 2 = 2 + 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm
  autogeneralize Mul.mul (α := ℕ) in mult_comm -- generalize all, separately
  specialize mult_comm.Gen Add.add Add.add Nat.add_comm 1 2
  assumption

example :  1 * 2 = 2 * 1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = m * n :=  Nat.mul_comm
  autogeneralize (HMul.hMul) in mult_comm at occurrences [1] -- generalize at first occurrence
  specialize mult_comm.Gen Mul.mul Nat.mul_comm 1 2
  assumption

example :  1 + 2 = (2 + 1)*1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = (m * n) * 1 :=  by {intros a b; rw [Nat.mul_one]; apply Nat.mul_comm}
  autogeneralize (HMul.hMul) in mult_comm at occurrences [1 3] -- generalize just at first and third occurrences, separately
  specialize mult_comm.Gen Add.add Add.add (Nat.mul_one) Nat.add_comm 1 2 -- ideally shouldnt say "mul_one"
  assumption

example :  1 * 2 = (2 * 1)*1 := by
  let mult_comm :  ∀ (n m : ℕ), n * m = (m * n) * 1 :=  by {intros a b; rw [Nat.mul_one]; apply Nat.mul_comm}
  autogeneralize (HMul.hMul) in mult_comm at occurrences [1 2] -- generalize just at first and second occurrences, separately
  specialize mult_comm.Gen Mul.mul Mul.mul (Nat.mul_one) Nat.mul_comm 1 2
  assumption

/--
Generalizing an operator that requires commutativity and associativity.
Generalizes all instances of * in the same way.
-/
example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let mult_permute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize_basic Mul.mul in mult_permute
  specialize mult_permute.Gen (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption

/--
Generalizing an operator that requires commutativity and associativity.
Generalizes all instances of * separately.
-/
example :  1 + (2 + 3) = 2 + (1 + 3) := by
  let mult_permute :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize Mul.mul (α := ℕ) in mult_permute
  specialize mult_permute.Gen (.+.) (.+.) (.+.) (.+.) Nat.add_assoc Nat.add_comm 1 2 3
  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING WITH COMPUTATION RULES
Demonstration that compatible proofs must use deduction rules, not computation rules
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/


/--
An example where only deduction rules are used, so the proof generalizes.
-/
example := by
  let two_times_three_is_even : Even (2*3) := by {unfold Even; apply Exists.intro 3; rw [two_mul]}
  autogeneralize 3 in two_times_three_is_even
  assumption

theorem six_is_even' : Even 6 := by {unfold Even; use 3}
example := by
  let two_times_three_is_even : Even (2*3) := by
    simp only [even_two, Even.mul_right]
    -- simp only [Nat.reduceMul]; apply six_is_even
  -- autogeneralize 3 in two_times_three_is_even -- throws error b/c of computation rule
  assumption

/--
An example where "3" doesn't show up in the proof term (due to use of the computation rule reduceMul), so the proof doesn't generalize.
-/
theorem six_is_even'' : Even 6 := by {unfold Even; use 3}
example := by
  let two_times_three_is_even : Even (2*3) := by
    decide
  -- autogeneralize 3 in two_times_three_is_even -- throws error b/c of computation rule
  assumption

/--
-- PROVING WITHOUT COMPUTATION RULES
-/
theorem six_is_even''' : Even (3+3) := by
  apply even_add_self 3
example : Even 4 := by
  autogeneralize (3:ℕ) in six_is_even''' -- extracts out comp rule
  specialize six_is_even'''.Gen 2
  assumption

/--
-- PROVING WITH COMPUTATION RULES
-/
theorem six_is_even'''' : Even (3+3) := by
  -- rw [@Nat.even_iff]
  -- simp only [Nat.reduceAdd] -- the computation rule
  exact Nat.even_iff.mpr (rfl) -- rfl is a computation rule

example : Even 4 := by
  autogeneralize (3:ℕ) in six_is_even'''' -- extracts out comp rule
  -- specialize six_is_even''''.Gen 1 3
  -- simp at six_is_even''''.Gen
  -- assumption
  trivial
