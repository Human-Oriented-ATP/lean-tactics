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
