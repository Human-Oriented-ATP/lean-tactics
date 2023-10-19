import Lean.Server.Rpc.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.OfRpcMethod
import Std.Lean.Position
import Mathlib
import Std.Util.TermUnsafe
import Std.CodeAction.Attr
import TreeMoves.Tree

/-!

# The motivated proof panel

This file contains code for
- Buttons for inserting text into the editor
- The `motivated_proof_move` attribute for
  tagging and registering new motivated proof moves
- The `motivated_proof` tactic which
  displays the motivated proof panel alongside the
  problem state.

-/

namespace ProofWidgets
open Lean Server Elab Command Lsp

/-- Parameters for editing the text document through the Language Server Protocol.
    These are used by the button to make edits on click and change the cursor position. -/
structure EditParams where
  edit : Lsp.TextDocumentEdit
  newCursorPos? : Option Lsp.Position := none
deriving RpcEncodable

namespace EditParams

/-- Replace `range` with `newText` and then place the cursor at the end of the new text. -/
def ofReplaceRange (meta : Server.DocumentMeta) (range : Lsp.Range)
    (newText : String) : EditParams :=
  let edit := { textDocument := { uri := meta.uri, version? := meta.version }
                edits        := #[{ range, newText }] }
  let newCursorPos? := some {
    line := range.start.line
    character := range.start.character + newText.codepointPosToUtf16Pos newText.length
  }
  { edit, newCursorPos? }

/-- Insert a line with the given text, a useful special case of replacing a range. -/
def insertLine (meta : Server.DocumentMeta) (line : Nat) 
    (indent : Nat) (text : String) : EditParams :=
  let newText := "".pushn ' ' indent ++ text
  let pos := { line := line, character := 0 }
  EditParams.ofReplaceRange meta ⟨pos, pos⟩ newText

end EditParams


section DynamicButton

/-!

## Buttons

Most of the interaction in the point-and-click interface happens through buttons.
These are implemented as a React JS Component using `ProofWidgets`.
-/

-- TODO: Make these inductive types
/-- Styling parameters for buttons. -/
structure DynamicButtonStylingProps where
  variant : String := "outlined" -- 'text' | 'outlined' | 'contained'
  color : String := "primary" -- 'inherit' | 'primary' | 'secondary' | 'success' | 'error' | 'info' | 'warning'
  size : String := "medium" -- 'small' | 'medium' | 'large'

/-- The parameters that can be supplied to a button.
    Buttons can optionally insert text in the editor and render HTML on click.
    They can also be made to vanish on click. -/
structure DynamicButtonProps extends DynamicButtonStylingProps where
  label : String
  edit? : Option EditParams := none
  html? : Option Html := none
  vanish : Bool := false
  key   :=   label  -- this is needed for technical reasons to do with rendering React components
deriving RpcEncodable

/-- The implementation of the button as a component with the logic specified in the JavaScript code.
    Run `lake build customWidgetJs` to build this JavaScript file. -/
@[widget_module] def DynamicButton : Component DynamicButtonProps where
  javascript := include_str ".." / "build" / "js" / "dynamicButton.js"

/-- A wrapper around `DynamicButton` that requires an `Lsp.Range` instead of `EditParams`.
    This is usually much more convenient in practice. -/
structure DynamicEditButtonProps extends DynamicButtonStylingProps where
  label : String
  range? : Option Lsp.Range := none
  insertion? : Option String := none
  html? : Option Html := none
  vanish : Bool := false
deriving RpcEncodable

/-- The logic for generating a `DynamicButton` from the `DynamicEditButtonParams`. -/
@[server_rpc_method]
def DynamicEditButton.rpc (props : DynamicEditButtonProps) : RequestM (RequestTask Html) := do
  RequestM.asTask do
    let doc ← RequestM.readDoc
    let editParams? : Option EditParams := do 
      let range ← props.range?
      let insertion ← props.insertion?
      return .ofReplaceRange doc.meta range insertion
    return .ofComponent DynamicButton (children := #[])
      { label := props.label
        edit? := editParams?
        html? := props.html?
        vanish := props.vanish
        variant := props.variant
        color := props.color
        size := props.size }

/-- The implementation of `DynamicEditButtons` using `DynamicEditButtons.rpc`. -/
@[widget_module] def DynamicEditButton : Component DynamicEditButtonProps :=
  mk_rpc_widget% DynamicEditButton.rpc

end DynamicButton


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
  let some goal := goal? | return Task.pure <| .ok <| .element "span" #[] #[.text "No goals found"]
  goal.ctx.val.runMetaM {} do
    let infoviewActions := infoviewActionExt.getState (← getEnv)
    let motivatedProofMoves ← infoviewActions.filterMapM 
      fun (_, action) ↦ (action props').run
    return Task.pure <| .ok <| .element "div" #[("id", "Grid")] motivatedProofMoves

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
              edit? := some <| .ofTextEdit doc.meta.uri {
                range := ⟨stxEnd, stxEnd⟩, newText := "\n  motivated_proof\n  "
              } } }]
      |         _          => return #[]

end MotivatedProofMode
