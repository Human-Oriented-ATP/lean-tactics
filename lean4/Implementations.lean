import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Logic.Basic

-- 1. expand (version 1)
macro "expand1" h:ident : tactic => `(tactic| dsimp [$h:ident])

def f (x: Nat) := x
def g (x: Nat) := x + 2

example (x : Nat) : f (g x) = x + 2 := by
  expand1 f -- same as unfold g
  expand1 g -- same as unfold f

-- 2. expand (version 2) 

-- 4. targetConjunctionSplit"
macro "targetConjunctionSplit" : tactic => `(tactic| apply And.intro) -- `(tactic| constructor)

example (h : p ∧ q) : q ∧ p := by
  targetConjunctionSplit -- same as `apply And.intro`
  . exact h.right
  . exact h.left

-- 5. targetImplicationSplit
macro "targetImplicationSplit" h:ident : tactic => `(tactic| intro $h:ident)

example (p : Prop) : p → p := by
  targetImplicationSplit h -- same as `intro h`
  exact h

-- 3. hypothesisConjunctionSplit
macro "hypothesisConjunctionSplit" h:ident hl:ident hr:ident : tactic => `(tactic| have ⟨$hl, $hr⟩ := $h)

-- before
example (h : p ∧ q) : q ∧ p := by
  have hq := h.right
  have hp := h.left
  exact ⟨hq, hp⟩

-- after
example (h : p ∧ q) : q ∧ p := by
  hypothesisConjunctionSplit h hp hq -- same as `have hq := h.right; have hp := h.left`
  exact ⟨hq, hp⟩

-- 7. hypothesisDisjunctionSplit
macro "hypothesisDisjunctionSplit" h:ident hl:ident hr:ident : tactic => `(tactic| cases' $h:ident with $hl:ident $hr:ident)

-- before
example (h : p ∨ q) : q ∨ p := by
  apply Or.elim h
  . intro hp 
    exact Or.inr hp
  . intro hq
    exact Or.inl hq

-- after
example (h : p ∨ q) : q ∨ p := by
  hypothesisDisjunctionSplit h hp hq
  . exact Or.inr hp
  . exact Or.inl hq

-- If the current target is `¬P`, then `P` is added to the list of hypotheses and the target is replaced by `False`
macro "negateTarget" h:ident : tactic => `(tactic| intro $h:ident)

-- If `h : ¬ P` is a hypothesis and the goal is `False`, then replace the goal with `P`
macro "negateHypothesis" h:ident : tactic => `(tactic| apply $h <;> clear $h) 

example (h : ¬ P) (hP: P) : False := by
  negateHypothesis h
  exact hP

-- If `h : P → Q` is a hypothesis and the goal is `Q`, then replace the goal with `P`
macro "backwardsReasoning" h:ident : tactic => `(tactic| apply $h <;> clear $h)

example (h : P → Q) (hP : P) : Q := by 
  backwardsReasoning h
  exact hP  

lemma makeOrExclusiveLemma : P ∨ Q ↔ P ∨ (¬ P → Q) := by 
  apply iff_def.mpr ⟨_, _⟩
  . rw[or_iff_not_imp_left]
    exact Or.intro_right P
  . intro h; cases' h with hP hPQ
    . exact Or.inl hP
    . exact Iff.mpr or_iff_not_imp_left hPQ
  
macro "makeOrExclusive" : tactic => `(tactic| rw [makeOrExclusive])

example : P ∨ Q ↔ P ∨ (¬ P → Q) := by
  rw [makeOrExclusiveLemma]

-- 9. disjunctionToImplication
lemma disjunctionToImplicationLemma : P ∨ Q ↔ (¬ P → Q) := by
  apply Iff.intro
  . intro h
    cases' h with hp hq
    . intro nh; contradiction
    . intro nh; exact hq
  . intro h
    apply Or.elim (em P)
    . intro hp
      apply Or.inl hp
    . intro hnp
      have hq := h hnp
      apply Or.inr hq

macro "disjunctionToImplicationLemma" : tactic => `(tactic| rw [disjunctionToImplicationLemma])

example : P ∨ Q ↔ (¬ P → Q) := by
  rw [disjunctionToImplicationLemma] -- also works without rw

-- 26. name
macro "name" p:ident q:ident : tactic => `(tactic| have $q:ident := $p:ident)

example (P : Prop) : P → P := by
  intro hp
  name hp q -- same as `have q := hp`
  exact q
