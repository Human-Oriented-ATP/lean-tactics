import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Logic.Basic

-- 1. expand (version 1)
-- macro "expand1" : tactic => `(tactic | {apply delta; apply})

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

-- macro "hypothesisConjunctionSplit" h:ident hl:ident hr:ident : tactic => `(tactic| {have $hl := ($h).left; have $hr := ($h).right})
macro "hypothesisConjunctionSplit" h:ident hl:ident hr:ident : tactic => `(tactic| {have ⟨$hl, $hr⟩ := $h; exact ⟨$hr, $hl⟩})
-- macro "hypothesisConjunctionSplit" h:ident hl:ident hr:ident : tactic => `(tactic| {cases $h with | intro $hl $hr => })

-- prototype 
example (h : p ∧ q) : q ∧ p := by
  have h1 := h.right
  have h2 := h.left
  exact ⟨h1, h2⟩
  -- . exact And.right h
  -- . exact And.left h

example (h : p ∧ q) : q ∧ p := by
  cases h with
  | intro p q =>
    exact ⟨q, p⟩

example (h : p ∧ q) : q ∧ p := by
  hypothesisConjunctionSplit h hl hr

-- this seems to be the kind of tactic which needs the next move
-- the second macro doesn't work unless we supply the tactic a
-- macro "hypothesisDisjunctionSplit" h:ident : tactic => `(tactic| {apply Or.elim $h:ident})
macro "hypothesisDisjunctionSplit" h:ident a:ident b:ident : tactic => `(tactic| cases' $h:ident with $a:ident $b:ident)

example (h : p ∨ q) : q ∨ p := by
  apply Or.elim h
  . intro hp 
    exact Or.inr hp
  . intro hq
    exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  hypothesisDisjunctionSplit h a b
  . exact Or.inr a
  . exact Or.inl b

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
