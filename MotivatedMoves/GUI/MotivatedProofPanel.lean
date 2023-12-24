import Lean.Server.Rpc.Basic
import ProofWidgets.Data.Html
import Std.Lean.Position
import Std.Util.TermUnsafe
import Std.CodeAction.Attr
import MotivatedMoves.ProofState.Tree
import MotivatedMoves.GUI.DynamicEditButton

/-!

# The motivated proof panel

This file contains code for
- The `motivated_proof_move` attribute for
  tagging and registering new motivated proof moves
- The `motivated_proof` tactic which
  displays the motivated proof panel alongside the
  problem state.

-/

namespace ProofWidgets

open Lean Server Elab Command Lsp

section InfoviewAction

/-!

## Infoview actions

The motivated proof panel is customised according to the 
pattern of selections made by the user in the goal state.

The `InfoviewActionProps` structure contains most of the information
about these selections, along with other relevant details.

`InfoviewAction`s are the main abstraction used to decide 
the contents of the motivated proof panel.
An `InfoviewAction` is defined as a function that takes in
`InfoviewActionProps` and optionally returns a piece of HTML code
(which is usually just a button).
The `InfoviewAction`s are registered and stored through the
`motivated_proof_move` attribute. 

The panel is rendered by reading in the current `InfoviewActionProps`,
applying it to all the `InfoviewAction`s registered in the environment
and then rendering the resulting snippets of HTML together in a single `div` block.

The HTML output of an `InfoviewAction` is computed in the `MetaM` monad,
which makes it possible to encode sophisticated logic on when to display
a piece of HTML and what to display in it.

-/

structure InfoviewActionProps extends PanelWidgetProps where
  range : Lsp.Range
deriving RpcEncodable

abbrev InfoviewAction := InfoviewActionProps → OptionT MetaM Html

def mkInfoviewAction (n : Name) : ImportM InfoviewAction := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck InfoviewAction opts ``InfoviewAction n

initialize infoviewActionExt : 
    PersistentEnvExtension Name (Name × InfoviewAction) (Array (Name × InfoviewAction)) ←
  registerPersistentEnvExtension {
    mkInitial := pure .empty
    addImportedFn := Array.concatMapM <| Array.mapM <| fun n ↦ do return (n, ← mkInfoviewAction n)
    addEntryFn := Array.push
    exportEntriesFn := .map Prod.fst
  }

initialize registerBuiltinAttribute {
  name := `motivated_proof_move
  descr := "Declare a new motivated proof move to appear in the point-and-click tactic panel."
  applicationTime := .afterCompilation
  add := fun decl stx _ => do
    Attribute.Builtin.ensureNoArgs stx
    if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
    modifyEnv (infoviewActionExt.addEntry · (decl, ← mkInfoviewAction decl))
}

@[server_rpc_method]
def MotivatedProofPanel.rpc (props : InfoviewActionProps) : RequestM (RequestTask Html) := do
  let props' := { props with range := ⟨props.range.end, props.range.end⟩ }
  let goal? : Option Widget.InteractiveGoal := do
    if props.selectedLocations.isEmpty then
      props.goals[0]?
    else
      let selectedLoc ← props.selectedLocations[0]?
      props.goals.find? (·.mvarId == selectedLoc.mvarId)
  let some goal := goal? | return .pure <| .element "span" #[] #[.text "No goals found"]
  goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let infoviewActions := infoviewActionExt.getState (← getEnv)
      let motivatedProofMoves ← infoviewActions.filterMapM 
        fun (_, action) ↦ (action props').run
      return .pure <| .element "div" #[("id", "Grid")] motivatedProofMoves

@[widget_module] def MotivatedProofPanel : Component InfoviewActionProps :=
  mk_rpc_widget% MotivatedProofPanel.rpc

end InfoviewAction


section MotivatedProofMode

/-!

## The `motivated_proof` tactic

The user finally interacts with the motivated proof panel
using the `motivated_proof` tactic, which renders the
panel of motivated proof moves alongside the goal state in the infoview.

-/

open Elab Tactic
open scoped Json

syntax (name := motivatedProofMode) "motivated_proof" tacticSeq : tactic

-- def evalTacticSeqInterspersedWith (τ : TSyntax `tactic) : TSyntax ``Parser.Tactic.tacticSeq → TacticM Unit
--   | `(Parser.Tactic.tacticSeq| $[$tacs]*)
--   | `(Parser.Tactic.tacticSeq| { $[$tacs]* }) => do
--     evalTactic τ
--     for tac in tacs do
--       evalTactic τ
--       evalTactic tac
--       evalTactic τ
--   |           _             => pure ()

@[tactic motivatedProofMode] def motivatedProofModeImpl : Tactic
| stx@`(tactic| motivated_proof%$motivated_proof $seq) => do
    let some ⟨stxStart, stxEnd⟩ := (← getFileMap).rangeOfStx? stx | return ()
    let defaultIndent := stxStart.character + 2
    let indent : Nat :=
      match seq with
      | `(Parser.Tactic.tacticSeq| $[$tacs]*) =>
        if tacs.size = 0 then
          defaultIndent
        else match stx.getHeadInfo with
          | .original _ _ trailing _ =>
            trailing.toString |>.dropWhile (· = '\n') |>.length
          |  _  => panic! s!"Could not extract indentation from {stx}."
      |       _      => panic! s!"Could not extract tactic sequence from {seq}." 
    let pos : Lsp.Position := { line := stxEnd.line + 1, character := indent }
    let range : Lsp.Range := ⟨stxEnd, pos⟩
    savePanelWidgetInfo stx ``MotivatedProofPanel do
      return json% { range : $(range) }
    Tree.workOnTreeDefEq pure -- this turns the goal into a tree initially
    evalTacticSeq seq
|                 _                    => throwUnsupportedSyntax

@[command_code_action Parser.Term.byTactic]
def startMotivatedProof : Std.CodeAction.CommandCodeAction :=
  fun _ _ _ tree ↦ do
    let some info := tree.findInfo? (match ·.stx with | `(by $_) => .true | _ => .false) | return #[]
    let doc ← RequestM.readDoc
    match info.stx with
      | stx@`(by $_tacs:tacticSeq) => 
        let eager : Lsp.CodeAction := {
          title := "Start a motivated proof."
          kind? := "quickfix",
          isPreferred? := some .true
        }
        return #[{
          eager
          lazy? := some do
            let some ⟨_, stxEnd⟩ := doc.meta.text.rangeOfStx? stx | return eager
            return { eager with
              edit? := some <| .ofTextEdit ⟨doc.meta.uri, doc.meta.version⟩ {
                range := ⟨stxEnd, stxEnd⟩, newText := "\n  motivated_proof\n  "
              } } }]
      |         _          => return #[]

end MotivatedProofMode
