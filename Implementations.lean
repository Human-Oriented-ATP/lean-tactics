import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Logic.Basic
import Mathlib.Tactic.Replace
import Mathlib.Tactic.Set
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormCast
import ProofWidgets.Demos.Conv

open Lean


def PosAtom' : Char → MacroM (TSyntax `term)
| 'A' => `(λ x ↦ (?_ : _ → _)  x) -- argument
| 'F' => `(λ x ↦ (x  : _ → _) ?_) -- function
| 'T' => `(λ x ↦ ?_ → x)  -- target
| 'H' => `(λ x ↦ x → ?_) -- hypothesis
-- | 'λ' => `(λ x ↦ λ ?_ ↦ x)
-- | 'l' => `(λ x ↦ let _ := ?_ ;  x)
-- | 'L' => `(λ x ↦ let _ := x  ; ?_)
| _ => Macro.throwUnsupported

def FindMotive : String → MacroM (TSyntax `term) :=
λ ⟨s⟩ ↦ do
  let atoms ← s.mapM PosAtom'
  atoms.foldlM (λ x y ↦ `($x ∘ $y)) (init := ← `(id))

lemma decompose {g : α  → β} {f : β  → γ} : (f ∘ λ x ↦ g x) a = f (g a) := rfl
lemma deid : id a = a := rfl
macro "expandLambdaComposition" : tactic => `(tactic| ((iterate refine decompose.mpr ?_); refine deid.mpr ?_))

macro "FromSubEquality" s:str h:term : tactic => do 
  let mot ← FindMotive s.getString
  `(tactic| refine congrArg $mot $h)

example (h : a = b) : (2 + a + 3) = (2 + b + 3) := by
  FromSubEquality "FAA" h



-- TODO fix this bug below
macro "rewriteAt" s:str h:Parser.Tactic.rwRule : tactic => do
  let l_arrow := h.raw[0]
  let h := ⟨h.raw[1]⟩
  let h := if l_arrow.isNone -- if l_arrow is ← or <- then apply Eq.symm to h
    then h
    else ← `(Eq.symm $h)
  let mot ← FindMotive s.getString
  `(tactic| (refine @Eq.substr _ $mot _ _ $h ?_; expandLambdaComposition))

-- notice the difference in behaviour between using ?_ or _ for the hole:
example {p : ℕ  → ℕ → Prop} (h₁ : a = b) : p a a := by
  refine @Eq.substr _ (λ x ↦ (?_ : _ → _)  x) _ _ h₁ ?_
  expandLambdaComposition -- ⊢ p a b
  sorry

example {p : ℕ  → ℕ → Prop} (h₁ : a = b) : p a a := by
  refine @Eq.substr _ (λ x ↦ ( _ : _ → _)  x) _ _ h₁ ?_
  expandLambdaComposition -- ⊢ p b b
  sorry
-- apparently it is crucial to use ?_


-- notice that it is possible to have implicit variables in the rewrite rule :)
-- they must however be specific enough so that the resulting type can be infered.

example {p q : ℕ  → ℕ → Prop} (h₁ : a = b) (h₂ : ∀ {q}, q = p) : ℝ → (q b a → p a a) ∧ True := by
  rewriteAt "TFATA" h₁
  rewriteAt "TFAHA" h₁
  rewriteAt "TFAHFF" h₂
  rewriteAt "TFAHFA" ← h₁
  intro _
  simp

example {p q : ℕ  → ℕ → Prop}  (temp : ((p a b → p a b)) = True) (h₁ : a = b) (h₂ : ∀ {q}, q = p) : ℝ → (q b a → p a a) ∧ True := by 
with_panel_widgets [ConvPanel]
  conv =>
  -- `ℝ` is `/0/1/0`
  -- `(q b a → p a a) ∧ True` is `/0/1/1`
  -- `True` is `/0/1/1/1`
  -- `p a a` is `/0/1/1/0/1/1`
  -- It seems that the first number is just a marker of the current goal/something else and should be deleted
  -- The rest follows very similarly to Jovan's program
  -- This sequence in these cases is just a binary tree in syntax, just need to map into to Jovan's notation
  rw [h₁]
  sorry

-- This tactic will not rewrite within dependent types unfortunately
example (h : ∀ {n}, (a = n) = True) : ∀ n : ℕ, a = n := by
  -- `rewriteAt "T" h` throws an error 
  sorry


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
macro "hypothesisImplicationSplit" h:ident q:ident : tactic => `(tactic| (refine (λ $q ↦ ?_) ($h ?_)))

example (hp : p) (h : p → q) : q := by
  hypothesisImplicationSplit h hq
  . exact hq
  . exact hp 

example {P Q : Nat → Prop} (hP: ∀ x, P x): ∀ x, Q x := by
  intro x
  have h1 : P ?a → Q ?a := sorry
  hypothesisImplicationSplit h1 hq
  on_goal 2 => convert h1 _
  all_goals {apply hP}
    -- want to instantiate ?a with x but they are in different proof states, need to think of a fix

/-- If `h : P ∨ Q` is a hypothesis, then replace it by `p : P` in one branch and replace it by `q : Q` in another branch-/
macro "hypothesisDisjunctionSplit" h:ident p:ident q:ident : tactic => `(tactic| 
  (refine Or.elim $h (λ $p ↦ ?_) (λ $q ↦ ?_);
    (try rewrite [show $h = Or.inl $p from rfl] at *);
    (on_goal 2 => try rewrite [show $h = Or.inr $q from rfl] at *))
  <;> clear $h)

example (h : p ∨ q) : q ∨ p := by
  hypothesisDisjunctionSplit h a b
  . exact Or.inr a
  . exact Or.inl b
  rewrite

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
  apply Iff.intro
  . rw[or_iff_not_imp_left]
    exact Or.intro_right P
  . intro h; cases' h with hP hPQ
    . exact Or.inl hP
    . exact Iff.mpr or_iff_not_imp_left hPQ
  
/-- `makeOrExclusive (at h)` rewrites the goal/hypothesis of form `P ∨ Q` into `P ∨ (¬ P → Q)` -/
macro "makeOrExclusive" loc:(Parser.Tactic.location)? : tactic => 
  `(tactic| rewrite [makeOrExclusiveLemma] $(loc)?)

example (h : P ∨ Q) : P ∨ Q := by
  makeOrExclusive at h
  makeOrExclusive
  sorry

/-- If the current goal is of the form `P ∨ Q`, then replace it by `¬ P → Q` -/
macro "disjunctionToImplicationLemma" loc:(Parser.Tactic.location)? : tactic => `(tactic| rewrite [or_iff_not_imp_left] $(loc)?)

example (h : P ∨ Q) : P ∨ Q ↔ (¬ P → Q) := by 
  disjunctionToImplicationLemma at h
  disjunctionToImplicationLemma
  rfl

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

/- If `h : P` and the type `P` is also of type `Q`, then coerce will give `h : Q`.-/
macro "coerce" : tactic => `(tactic | norm_cast)

example : ((42 : ℕ) : ℤ) = 42 := by
  coerce

/-- If `p : P` and `q : Q` are hypotheses, replace `p` and `q` by `pq : P ∧ Q`. -/
macro "combine" p:ident q:ident pq:ident : tactic => `(tactic | (have $pq := And.intro $p $q; clear $p $q))

example (P Q : Prop) (p : P) (q : Q): P ∧ Q := by
  combine p q pq -- same as have pq := And.intro p q
  exact pq

/-- If `h` is a hypothesis and the target is `h`, then `cancel h` will finish off the proof.-/
macro "cancel" h:ident : tactic => `(tactic| exact $h <;> clear $h)

example (P : Prop) (p : P) : P := by
  cancel p
  
-- `TODO` add support for holes 
/-- `instantiate h a₁ ... aₙ as h'`
instantiates the hypothesis `h` with constants `a₁, ..., aₙ` in this order` and adds it as a new hypothesis `h'`-/
macro "instantiate" S:ident "[" h:term,* "] as" T:ident : tactic =>
  `(tactic| have $T:ident := @$S $h:term*)

example {P : Nat → Nat → Prop} (h : ∀ x y, P x y) : True := by
  instantiate h [2, 3] as h'
  trivial


