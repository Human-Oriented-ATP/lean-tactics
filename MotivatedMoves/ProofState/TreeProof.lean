import Lean
import Qq

open Lean Qq Elab Meta Term

namespace MotivatedTree

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

def TreeProof.compose (step₁ step₂ : ProofStep pol) : ProofStep pol := fun tree ↦ do
  let treeProof ← step₁ tree
  treeProof.map step₂

end MotivatedTree
