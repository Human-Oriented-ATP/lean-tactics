import MotivatedMoves.Moves.Basic
import MotivatedMoves.Moves.Panel
import MotivatedMoves.Moves.TreeInduction
import MotivatedMoves.Moves.TreeNaming
import MotivatedMoves.Moves.TreeRewriteOrd
import MotivatedMoves.Moves.TreeSearch
import MotivatedMoves.Moves.TreeContradiction

open Lean ProofWidgets Elab Tactic Jsx

namespace Tree

@[new_motivated_proof_move]
def treeApplyMove : MotivatedProof.Suggestion
  | #[pos₁, pos₂] => do
    let tac ← `(tactic| tree_apply $(quote pos₁) $(quote pos₂))
    let _ ← OptionT.mk <| withoutModifyingState <|
              try? <| evalTactic tac
    return {
      description := "Apply",
      code := do
        let keepHyp ← askUserBool 0 <p>Would you like to preserve the selected hypothesis?</p>
        return s!"tree_apply{if keepHyp then "" else "'"} {pos₁} {pos₂}"
    }
  | _ => failure

@[new_motivated_proof_move]
def treeUnifyMove : MotivatedProof.Suggestion
  | #[pos] => withMainContext do
      let (goalOuterPosition, goalPos) := Tree.splitPosition pos.toArray.toList
      unless (← Tree.withTreeSubexpr (← getMainTarget) goalOuterPosition goalPos (fun _ x => pure x))
      matches Expr.app (.const ``Eq _) _ do failure
      return some {
        description := "Unify",
        code := return s!"lib_apply refl {pos}"
      }
  | _ => failure

elab "skip_lib_apply" : tactic => pure ()

@[new_motivated_proof_move]
def treeLibraryApplyMove : MotivatedProof.Suggestion
  | #[pos] => return {
    description := "Apply a library result",
    code := do
    let keepHyp? ← askUserBool 0 <text>Would you like to keep the closed goal as a hypothesis?</text>
    let libSuggestionsGrouped ← Tree.librarySearchApply keepHyp? (pos.toArray.toList) (← getMainTarget)
    let libSuggestions := libSuggestionsGrouped.concatMap fun («matches», score) ↦ («matches».map (·, score))
    let resultsCount :=
      if libSuggestions.size = RefinedDiscrTree.maxResultsCap then
        s!"at least {RefinedDiscrTree.maxResultsCap}"
      else
        s!"{libSuggestions.size}"
    let chooseLibApply ← askUserBool 0 <p>{.text s!"There are {resultsCount} results in the library that match the selection.\n Would you like to retrieve one at random?"}</p>
    if chooseLibApply then
      let (name, diffs, tacticCall) ← IO.randSampleWeighted libSuggestions.toList
      let confirmLibSuggestion ← askUserBool 0 <| .element "div" #[] #[
        <text>The randomly chosen result is</text>,
        <br />, ← name.renderWithDiffs diffs, <br />,
        <text>Would you like to use this result?</text>]
      if confirmLibSuggestion then
        return tacticCall
      else
        return "skip_lib_apply"
    else
      return "skip_lib_apply"
  }
  | _ => failure

@[new_motivated_proof_move]
def treeContraposeMove : MotivatedProof.Suggestion
  | #[pos₁, pos₂] => do
    let tac ← `(tactic| tree_contrapose $(quote pos₁) $(quote pos₂))
    let _ ← OptionT.mk <| withoutModifyingState <|
      try? <| evalTactic tac
    return {
      description := "Contrapose",
      code := do
        let keepHyp ← askUserBool 0 <p>Would you like to keep the selected hypothesis?</p>
        return s!"tree_contrapose{if keepHyp then "" else "'"} {pos₁} {pos₂}"
    }
  | _ => failure

@[new_motivated_proof_move]
def treeInductionMove : MotivatedProof.Suggestion
  | #[pos] => withMainContext do
    let tac ← `(tactic| tree_induction $(quote pos))
    let _ ← OptionT.mk <| withoutModifyingState <|
      try? <| evalTactic tac
    return some {
      description := "Definitional induction/elimination",
      code := return s!"tree_induction {pos}"
    }
  | _ => failure

@[new_motivated_proof_move]
def treeLibraryInductionMove : MotivatedProof.Suggestion
  | #[pos] => do
    let libSuggestions ← Tree.librarySearchInduction (pos.toArray.toList) (← getMainTarget)
    if libSuggestions.isEmpty then failure
    return {
      description := "Custom induction/elimination",
      code := do
        let tacticCall ← askUserSelect 0 <p>Choose an induction principle</p> <| ← libSuggestions.toList.mapM
          fun (name, diffs, tacticCall) ↦ do
            return (tacticCall, <button>{← name.renderWithDiffs diffs}</button>)
        return tacticCall
    }
  | _ => failure

@[new_motivated_proof_move]
def treeNameMove : MotivatedProof.Suggestion
  | #[pos] =>
    return {
      description := "Name the selected expression"
      code := do
        let meta? ← askUserBool 0 <p>Would you like to name the expression as a meta-variable?</p>
        let name ← askUserString 0 <p>Enter a name for the variable</p>
        return s!"tree_name{if meta? then "_meta" else ""} {name} {pos}"
    }
  | _ => failure

@[new_motivated_proof_move]
def treeSimpMove : MotivatedProof.Suggestion
  | #[pos] => return {
    description := "Simplify"
    code := return s!"tree_simp {pos}"
  }
  | _ => failure

@[new_motivated_proof_move]
def treePushNegMove : MotivatedProof.Suggestion
  | #[pos] => withMainContext do
    let (goalOuterPosition, goalPos) := Tree.splitPosition pos.toArray.toList
    unless (← Tree.withTreeSubexpr (← getMainTarget) goalOuterPosition goalPos (fun _ x => pure x))
        matches Expr.app (.const ``Tree.Not _) _ do failure
    return some {
      description := "Push the negation"
      code := return s!"tree_push_neg {pos}"
    }
  | _ => failure

@[new_motivated_proof_move]
def treeRewriteMove : MotivatedProof.Suggestion
  | #[pos₁, pos₂] => do
    let tac ← `(tactic| tree_rewrite $(quote pos₁) $(quote pos₂))
    let _ ← OptionT.mk <| withoutModifyingState <|
              try? <| evalTactic tac
    return {
      description := "Rewrite",
      code := do
        let keepHyp ← askUserBool 0 <p>Would you like to preserve the selected hypothesis?</p>
        return s!"tree_rewrite{if keepHyp then "" else "'"} {pos₁} {pos₂}"
    }
  | _ => failure

@[new_motivated_proof_move]
def treeHypSwapMove : MotivatedProof.Suggestion
  | #[pos] => do
    let tac ← `(tactic| lib_rewrite Imp.swap $(quote pos))
    let _ ← OptionT.mk <| withoutModifyingState <|
              try? <| evalTactic tac
    return {
      description := "Swap the hypotheses",
      code := return s!"lib_rewrite Imp.swap {pos}"
    }
  | _ => failure

elab "skip_lib_rewrite" : tactic => pure ()

@[new_motivated_proof_move]
def treeLibraryRewriteMove : MotivatedProof.Suggestion
  | #[pos] => return {
    description := "Rewrite using a library result",
    code := do
    let libSuggestionsGrouped ← Tree.librarySearchRewrite (pos.toArray.toList) (← getMainTarget)
    let libSuggestions := libSuggestionsGrouped.concatMap fun («matches», score) ↦ («matches».map (·, score))
    let resultsCount :=
      if libSuggestions.size = RefinedDiscrTree.maxResultsCap then
        s!"at least {RefinedDiscrTree.maxResultsCap}"
      else
        s!"{libSuggestions.size}"
    let chooseLibRewrite ← askUserBool 0 <p>{.text s!"There are {resultsCount} results in the library that match the selection.\n Would you like to retrieve one at random?"}</p>
    if chooseLibRewrite then
      let (name, diffs, tacticCall) ← IO.randSampleWeighted libSuggestions.toList
      let confirmLibSuggestion ← askUserBool 0 <| .element "div" #[] #[
        <text>The randomly chosen result is</text>,
        <br />, ← name.renderWithDiffs diffs, <br />,
        <text>Would you like to use this result?</text>]
      if confirmLibSuggestion then
        return tacticCall
      else
        return "skip_lib_rewrite"
    else
      return "skip_lib_rewrite"
  }
  | _ => failure

@[new_motivated_proof_move]
def treeRewriteOrdMove : MotivatedProof.Suggestion
  | #[pos₁, pos₂] => do
    let tac ← `(tactic| tree_rewrite_ord $(quote pos₁) $(quote pos₂))
    let _ ← OptionT.mk <| withoutModifyingState <|
              try? <| evalTactic tac
    return {
      description := "Ordered Rewrite",
      code := do
        let keepHyp ← askUserBool 0 <p>Would you like to preserve the selected hypothesis?</p>
        return s!"tree_rewrite_ord{if keepHyp then "" else "'"} {pos₁} {pos₂}"
    }
  | _ => failure

elab "skip_lib_rewrite_ord" : tactic => pure ()

@[new_motivated_proof_move]
def treeOrderedLibraryRewriteMove : MotivatedProof.Suggestion
  | #[pos] => return {
    description := "Ordered rewrite using a library result",
    code := do
    let libSuggestionsGrouped ← Tree.librarySearchRewriteOrd (pos.toArray.toList) (← getMainTarget)
    let libSuggestions := libSuggestionsGrouped.concatMap fun («matches», score) ↦ («matches».map (·, score))
    let resultsCount :=
      if libSuggestions.size = RefinedDiscrTree.maxResultsCap then
        s!"at least {RefinedDiscrTree.maxResultsCap}"
      else
        s!"{libSuggestions.size}"
    let chooseLibRewrite ← askUserBool 0 <p>{.text s!"There are {resultsCount} results in the library that match the selection.\n Would you like to retrieve one at random?"}</p>
    if chooseLibRewrite then
      let (name, diffs, tacticCall) ← IO.randSampleWeighted libSuggestions.toList
      let confirmLibSuggestion ← askUserBool 0 <| .element "div" #[] #[
        <text>The randomly chosen result is</text>,
        <br />, ← name.renderWithDiffs diffs, <br />,
        <text>Would you like to use this result?</text>]
      if confirmLibSuggestion then
        return tacticCall
      else
        return "skip_lib_rewrite_ord"
    else
      return "skip_lib_rewrite_ord"
  }
  | _ => failure

@[new_motivated_proof_move]
def treeSearchMove : MotivatedProof.Suggestion
  | #[] => return {
    description := "Search for redundant hypotheses and targets",
    code := do return s!"tree_search"
  }
  | _ => failure

@[new_motivated_proof_move]
def treeUnfoldMove : MotivatedProof.Suggestion
  | #[pos] =>
    return {
      description := "Unfold",
      code := return s!"tree_rewrite_def {pos}"
    }
  | _ => failure


lemma forall_exists_unify (p : α → α → Prop) : (∀ a, p a a) → ∀ a, ∃ b, p a b :=
  fun h a => ⟨a, h a⟩

macro "unify_forall_exists" pos:treePos : tactic => `(tactic| lib_apply [1,1,1] $(Lean.mkIdent ``forall_exists_unify) $pos)

@[new_motivated_proof_move]
def treeUnifyForallExistsMove : MotivatedProof.Suggestion
  | #[pos] => do
    let tac ← `(tactic| unify_forall_exists $(quote pos))
    let _ ← OptionT.mk <| withoutModifyingState <|
      try? <| evalTactic tac
    return {
      description := "Unify existential with preceding universal variable",
      code := return s!"unify_forall_exists {pos}"
    }
  | _ => failure
