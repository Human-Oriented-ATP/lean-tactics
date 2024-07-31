import Lean
import Aesop
import Qq

open Lean Qq Elab Meta Term

namespace MotivatedTree

/-!

# Structural sharing in the tactic state

- The usual Lean tactic state is a list of meta-variables, each with its own local context.
- This means that changes to the local context of one meta-variable do not affect the local context of the others.
- This does not cause much of an issue while formalising known mathematical proofs, since one can always restructure the proof to change the local context before splitting into several goals.
- However, this becomes problematic when using Lean to *discover* new proofs, since one may want to operate on a variable that occurs in the local context of multiple meta-variables.
- The solution here is to represent the tactic state as a tree whose leaves are the open goals in the proofs and whose nodes contain the information of the variables in the local context of each goal.
- Operating on a variable in the local context of one goal affects other goals too, since the change is made to the nodes of the tree.

-/

abbrev Tree := Prop

inductive TreeProof (tree : Q(Tree)) : (polarity : Bool) → Sort _ where
  | treeEnd (treeProof : Q($tree)) : TreeProof tree true
  | treeForward (newTree : Q(Tree)) (proof : Q($newTree → $tree)) : TreeProof tree true
  | treeBackward (newTree : Q(Tree)) (proof : Q($tree → $newTree)) : TreeProof tree false

abbrev ProofStep (polarity : Bool) := (tree : Q(Tree)) → MetaM (TreeProof tree polarity)

/-- Apply a proof step to an existing tree proof. -/
def TreeProof.map (step : ProofStep pol) (proof : TreeProof tree pol) : MetaM (TreeProof tree pol) := do
  match pol, proof with
  | true, .treeEnd treeProof =>
    return .treeEnd treeProof
  | true, .treeForward newTree proof =>
    let newProof ← step newTree
    match newProof with
    | .treeEnd newTreeProof =>
      return .treeEnd q($proof $newTreeProof)
    | .treeForward newerTree newerTreeProof =>
      return .treeForward newerTree q($proof ∘ $newerTreeProof)
  | false, .treeBackward newTree proof =>
    let newProof ← step newTree
    match newProof with
    | .treeBackward newerTree newerTreeProof =>
      return .treeBackward newerTree q($newerTreeProof ∘ $proof)

def ProofStep.compose (step₁ step₂ : ProofStep pol) : ProofStep pol := fun tree ↦ do
  let treeProof ← step₁ tree
  treeProof.map step₂

class PFunctor (f : Prop → Prop) where
  map {p q : Prop} : (p → q) → f p → f q

class PFunctorContra (f : Prop → Prop) where
  comap {p q : Prop} : (p → q) → f q → f p

class PMonad (m : Prop → Prop) extends PFunctor m where
  pure {p : Prop} : p → m p
  bind {p q : Prop} : m p → (p → m q) → m q
  map := fun f x ↦ bind x (Function.comp pure f)

class PComonad (m : Prop → Prop) extends PFunctor m where
  extract {p : Prop} : m p → p
  extend {p q : Prop} : m p → (m p → q) → m q
  map := fun f x ↦ extend x (f ∘ extract)

class PMonadContra (m : Prop → Prop) extends PFunctorContra m where
  pure {p : Prop} : p → m p
  bind {p q : Prop} : m p → (m p → q) → m q

class PropBinder (P : Q(Prop → Prop)) where
  bind {tree : Q(Tree)} : TreeProof tree pol → TreeProof q($P $tree) pol

class PropBinderContra (P : Q(Prop → Prop)) where
  bind : TreeProof tree pol → TreeProof q($P $tree) !pol

instance {m : Q(Prop → Prop)} (_inst : Q(PMonad $m)) : PropBinder q($m) where
  bind
  | .treeEnd treeProof => .treeEnd q(PMonad.pure $treeProof)
  | .treeForward newTree proof => .treeForward q($m $newTree) q(PFunctor.map $proof)
  | .treeBackward newTree proof => .treeBackward q($m $newTree) q(PFunctor.map $proof)

instance {m : Q(Prop → Prop)} (_inst : Q(PFunctor $m)) : PropBinder q($m) where
  bind
  | .treeEnd treeProof => .treeForward q($m True) q(PFunctor.map <| fun _ ↦ $treeProof)
  | .treeForward newTree proof => .treeForward q($m $newTree) q(PFunctor.map $proof)
  | .treeBackward newTree proof => .treeBackward q($m $newTree) q(PFunctor.map $proof)

instance {m : Q(Prop → Prop)} (_inst : Q(PFunctorContra $m)) : PropBinderContra q($m) where
  bind
  | .treeEnd treeProof => .treeBackward q($m True) q(PFunctorContra.comap <| fun _ ↦ $treeProof)
  | .treeForward newTree proof => .treeBackward q($m $newTree) q(PFunctorContra.comap $proof)
  | .treeBackward newTree proof => .treeForward q($m $newTree) q(PFunctorContra.comap $proof)

instance (p : Prop) : PMonad (p → ·) where
  pure := fun x _ ↦ x
  bind := fun f g x ↦ g (f x) x

instance (p : Prop) : PComonad (p ∧ ·) where
  extract := And.right
  extend := fun ⟨x, y⟩ f => ⟨x, f ⟨x, y⟩⟩

instance (p : Prop) : PComonad (· ∧ p) where
  extract := And.left
  extend := fun ⟨x, y⟩ f => ⟨f ⟨x, y⟩, y⟩

instance (p : Prop) : PMonad (p ∨ ·) where
  pure := Or.inr
  bind
  | Or.inl x => fun _ ↦ Or.inl x
  | Or.inr y => fun f ↦ f y

instance (p : Prop) : PMonad (· ∨ p) where
  pure := Or.inl
  bind
  | Or.inl x => fun f ↦ f x
  | Or.inr y => fun _ ↦ Or.inr y

instance (p : Prop) : PFunctorContra (· → p) where
  comap := fun f x y ↦ x (f y)

end MotivatedTree
