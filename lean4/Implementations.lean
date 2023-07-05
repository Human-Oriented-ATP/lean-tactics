import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Logic.Basic
import Mathlib.Tactic.Replace
import Mathlib.Tactic.Set

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

-- before
example (h : p ∧ q) : q ∧ p := by
  cases h with
  | intro p q =>
    exact ⟨q, p⟩

example (h : p ∧ q) : q ∧ p := by
  hypothesisConjunctionSplit h hl hr

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
macro "backwardsReasoning" h:ident "[" x:term,* "]": tactic => `(tactic| (refine $h $x:term*; clear $h))

example (h : P₁ → P₂ → P₃ → Q) (hP₁ : P₁) (hP₂ : P₂) : Q := by 
  backwardsReasoning h [hP₁, hP₂, ?_]
  sorry

lemma makeOrExclusiveLemma : P ∨ Q ↔ P ∨ (¬ P → Q) := by 
  apply iff_def.mpr ⟨_, _⟩
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

macro "forwardsReasoning" h:ident "["x:ident,*"]" : tactic => `(tactic| replace $h:ident := $h:ident $x:ident *)

example {P Q R : Prop}(h: P → Q → R) (hP : P) (hQ: Q): R := by
  forwardsReasoning h [hP, hQ]
  exact h

-- 9. disjunctionToImplication
macro "disjunctionToImplicationLemma" : tactic => `(tactic| rw [or_iff_not_imp_left])

example : P ∨ Q ↔ (¬ P → Q) := by
  rw [or_iff_not_imp_left] -- also works without rw

-- 16. name
macro "name" p:ident q:ident : tactic => `(tactic| have $q:ident := $p:ident)

example (P : Prop) : P → P := by
  intro hp
  name hp q -- same as `have q := hp`
  exact q

-- 18. delete
macro "delete" p:ident : tactic => `(tactic| clear $p:ident)

example (P : Prop) : True := by
  delete P -- same as `clear P`
  trivial

-- 20. combine
macro "combine" pq:ident p:ident q:ident : tactic => `(tactic | have $pq:ident := And.intro $p:ident $q:ident)

example (P Q : Prop) (p : P) (q : Q): P ∧ Q := by
  combine pq p q -- same as have pq := And.intro p q
  exact pq

macro "hypothesisImplicationSplit" h:ident P:term Q:term : tactic => `(tactic| (have hP: $P := ?_; have hQ : $Q := ($h : ident) hP))

-- what we want the above macro to do (still a `TODO`)
-- might have to match metavariables
example {P Q : Nat → Prop} (h : ∀ x, P x → Q x) : True := by
  set Px : Prop := P _ with hP
  have hQ := h ?_ ?_
  sorry
  sorry