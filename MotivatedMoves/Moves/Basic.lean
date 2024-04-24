import Lean
import MotivatedMoves.Interaction.AskUser

open Lean Meta Elab Term Tactic

namespace MotivatedProof

structure Move where
  description : String
  code : TacticIM String

abbrev Suggestion := Array SubExpr.Pos → OptionT TacticM Move

def mkSuggestion (declName : Name) : ImportM Suggestion := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck Suggestion opts ``Suggestion declName

initialize suggestionExt : PersistentEnvExtension Name (Name × Suggestion) (Array (Name × Suggestion)) ←
  registerPersistentEnvExtension {
    mkInitial := pure .empty
    addImportedFn := Array.concatMapM <| Array.mapM <| fun n ↦ do return (n, ← mkSuggestion n)
    addEntryFn := Array.push
    exportEntriesFn := .map Prod.fst
  }

initialize registerBuiltinAttribute {
  name := `new_motivated_proof_move
  descr := "Declare a new motivated proof move to appear in the panel of suggestions."
  applicationTime := .afterCompilation
  add := fun decl stx _ => do
    Attribute.Builtin.ensureNoArgs stx
    if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
    modifyEnv (suggestionExt.addEntry · (decl, ← mkSuggestion decl))
}

end MotivatedProof

namespace Lean

open Lean ProofWidgets Widget Server Jsx

def Widget.CodeWithInfos.addDiffs (diffs : AssocList SubExpr.Pos DiffTag) (code : CodeWithInfos) : CodeWithInfos :=
  code.map fun info ↦
    match diffs.find? info.subexprPos with
      | some diff => { info with diffStatus? := some diff }
      |    none   =>   info

def Expr.renderWithDiffs (e : Expr) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do
  let e' := (← Widget.ppExprTagged e).addDiffs diffs
  return <InteractiveCode fmt={e'} />

def Name.renderWithDiffs (nm : Name) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do
  let env ← getEnv
  let some ci := env.find? nm | failure
  ci.type.renderWithDiffs diffs

end Lean

section Sampling

def List.findValueMatch (n : Nat) : List (α × Nat) → Option α
  | [] => none
  | (a, score) :: tail =>
      if n ≤ score then
        a
      else
        tail.findValueMatch (n - score)

def IO.randSampleWeighted (choices : List (α × Nat)) : IO α := do
  let aggregate := choices.foldl (init := 0) fun accum (_, score) ↦ accum + score
  let some choice := choices.findValueMatch (← IO.rand 1 aggregate) | IO.throwServerError "Expected a non-empty list of choices."
  return choice

end Sampling
