import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Logic.Basic
import Mathlib.Tactic.Replace
import Mathlib.Tactic.Set
import Mathlib.Tactic.PermuteGoals

/-- `expand1 S` unfolds `S` in the current goal using `dsimp`. -/
macro "expand1" h:ident : tactic => `(tactic| dsimp [$h:ident])

def f (x: Nat) := x
def g (x: Nat) := x + 2

example (x : Nat) : f (g x) = x + 2 := by
  expand1 f -- same as unfold g
  expand1 g -- same as unfold f

-- 2. expand (version 2) 

/-- If the current target is `P ∧ Q`, then replace it by the targets `P` and `Q`. -/
macro "targetConjunctionSplit" : tactic => `(tactic| refine And.intro ?_ ?_)

example (h : p ∧ q) : q ∧ p := by      
  targetConjunctionSplit
  . exact h.right
  . exact h.left
  

/-- If `h : P ∧ Q` is a hypothesis, replace it by the hypotheses `p : P` and `q : Q`. -/
macro "hypothesisConjunctionSplit" h:ident p:ident q:ident : tactic => `(tactic|
  (have ⟨$p, $q⟩ : _ ∧ _ := $h; try rw [show h = ⟨$p, $q⟩ from rfl] at *; clear $h))

example (h : p ∧ q) : q ∧ p := by
  hypothesisConjunctionSplit h hl hr
  exact ⟨hr,hl⟩


/-- If the current target is `P → Q`, then add `p : P` to the list of hypotheses and replace the target by `Q`. -/
macro "targetImplicationSplit" p:ident : tactic => `(tactic| intro $p:ident)

example (p : Prop) : p → p := by
  targetImplicationSplit h
  exact h


/-- If `h : P → Q` is a hypothesis, then add `q : Q` to the list of hypotheses, 
and create a new target `P` with the original list of hypotheses-/
macro "hypothesisImplicationSplit" h:ident q:ident : tactic => `(tactic| (refine (λ $q ↦ ?_) ($h ?_); clear $h))

example (hp : p) (h : p → q) : q := by
  hypothesisImplicationSplit h hq
  exact hq
  exact hp


/-- If `h : P ∨ Q` is a hypothesis, then replace it by `p : P` in one branch and replace it by `q : Q` in another branch-/
macro "hypothesisDisjunctionSplit" h:ident p:ident q:ident : tactic => `(tactic| 
  (refine Or.elim $h (λ $p ↦ ?_) (λ $q ↦ ?_);
    (try rw [show $h = Or.inl $p from rfl] at *);
    (on_goal 2 => try rw [show $h = Or.inr $q from rfl] at *))
  <;> clear $h)

example (h : p ∨ q) : q ∨ p := by
  hypothesisDisjunctionSplit h a b
  . exact Or.inr a
  . exact Or.inl b

-- when the target depends on h, hypothesisDisjunctionSplit still works:
example (h : p ∨ q) : Function.const  _ (q ∨ p) h := by
  hypothesisDisjunctionSplit h a b
  . exact Or.inr a
  . exact Or.inl b


/-- If the current target is `¬P`, then `negateTarget h` adds `h : P` to the list of hypotheses and replace the target by `False`. -/
macro "negateTarget" p:ident : tactic => `(tactic| refine λ $p:ident ↦ (?_ : False))

example : ¬False := by
  negateTarget h
  exact h

/-- If `h : ¬P` is a hypothesis and the goal is `False`, then replace the goal with `P` and delete `h`. -/
macro "negateHypothesis" h:ident : tactic => `(tactic| (refine ($h ?_ : False) ; clear $h)) 

example (h : ¬P) (hP : P) : False := by
  negateHypothesis h
  exact hP


/-- If `h : P₁ → .. → Pₙ → Q` is a hypothesis, `Q` is the target and `pᵢ : Pᵢ` are hypotheses or placeholders, 
then create a new goal `Pᵢ` for each placeholder `pᵢ` -/
macro "backwardsReasoning" h:ident "[" p:term,* "]": tactic => `(tactic| (refine $h $p:term *; clear $h))

example (h : P₁ → P₂ → P₃ → Q) (hP₁ : P₁) (hP₂ : P₂) (hP₃ : P₃) : Q := by 
  backwardsReasoning h [hP₁, ?_, hP₃]
  exact hP₂

/-- If `h : P₁ → .. → Pₙ → Q` and `pᵢ : Pᵢ` are hypotheses, replace `h` by `h : Q` and delete each `pᵢ`. -/
macro "forwardsReasoning" h:ident "["x:ident,*"]" : tactic => `(tactic| (replace $h:ident := $h:ident $x:ident * ; clear $x *))

example {P Q R : Prop}(h: P → Q → R) (hP : P) (hQ: Q): R := by
  forwardsReasoning h [hP, hQ]
  exact h

lemma makeOrExclusiveLemma : P ∨ Q ↔ P ∨ (¬ P → Q) := by 
  refine iff_def.mpr ⟨?_, ?_⟩
  . rw[or_iff_not_imp_left]
    exact Or.intro_right P
  . intro h; cases' h with hP hPQ
    . exact Or.inl hP
    . exact Iff.mpr or_iff_not_imp_left hPQ
  
-- make this also work on goals, currently only works on named hypotheses
macro "makeOrExclusiveHyp" h:ident : tactic => `(tactic| rw [makeOrExclusiveLemma] at $h:ident)

--temporarily two different macros for goals and hypotheses 
macro "makeOrExclusive" : tactic => `(tactic| rw [makeOrExclusiveLemma])

example (h : P ∨ Q) : P ∨ Q := by
  makeOrExclusiveHyp h
  makeOrExclusive
  sorry


/-- If the current goal is of the form `P ∨ Q`, then replace it by `¬ P → Q` -/
macro "disjunctionToImplicationLemma" : tactic => `(tactic| rw [or_iff_not_imp_left])

example : P ∨ Q ↔ (¬ P → Q) := by
  rw [or_iff_not_imp_left] -- also works without rw

  example : P ∨ Q ↔ (¬ P → Q) := by disjunctionToImplicationLemma

/-- `name h i` renames the hypothesis `h` to have name `i` without changing its body -/
macro "name" p:ident q:ident : tactic => `(tactic| (have $q:ident := $p:ident; clear $p))

example (P : Prop) : P → P := by
  intro hp
  name hp q
  exact q

/-- If `h : P` is a hypothesis, remove `h` from the list of hypotheses. -/
macro "delete" p:ident : tactic => `(tactic| clear $p)

example (P : Prop) : True := by
  delete P -- same as `clear P`
  trivial

/-- If `p : P` and `q : Q` are hypotheses, replace `p` and `q` by `pq : P ∧ Q`. -/
macro "combine" p:ident q:ident pq:ident : tactic => `(tactic | (have $pq := And.intro $p $q; clear $p $q))

example (P Q : Prop) (p : P) (q : Q): P ∧ Q := by
  combine p q pq -- same as have pq := And.intro p q
  exact pq