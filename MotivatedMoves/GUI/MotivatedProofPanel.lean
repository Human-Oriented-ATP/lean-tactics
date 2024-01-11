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
  displays the panel of motivated proof moves 
  alongside the problem state.

-/

namespace ProofWidgets

open Lean Server Elab Term Tactic Command Lsp

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

The HTML output of an `InfoviewAction` is computed in the `TacticM` monad,
which makes it possible to encode sophisticated logic on when to display
a piece of HTML and what to display in it.

-/

/-- The parameters taken by an `InfoviewAction`. -/
structure InfoviewActionProps extends PanelWidgetProps where
  /-- The range of the syntax to be replaced.
      This is used to determine the position of the new tactic insertions in the document.

      By convention, the range is from the end of the current tactic block
      to the expected start position of the new tactic (this is used to compute the whitespace correctly). -/
  range : Lsp.Range
deriving RpcEncodable

/-- An `InfoviewAction` is a procedure to optionally compute a piece of HTML
    based on the pattern of selections in the tactic state (which is roughly the infomation in `InfoActionProps`).
    
    This is used in the motivated proof panel to display a suggestion (usually in the form of an HTML button)
    based on the selections made. -/
abbrev InfoviewAction := InfoviewActionProps → OptionT TacticM Html

/-- Evaluate a name to an `InfoviewAction` defined in the environment. -/
def mkInfoviewAction (n : Name) : ImportM InfoviewAction := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck InfoviewAction opts ``InfoviewAction n

/-- A global register of `InfoviewAction`s. -/
initialize infoviewActionExt : 
    PersistentEnvExtension Name (Name × InfoviewAction) (Array (Name × InfoviewAction)) ←
  registerPersistentEnvExtension {
    mkInitial := pure .empty
    addImportedFn := Array.concatMapM <| Array.mapM <| fun n ↦ do return (n, ← mkInfoviewAction n)
    addEntryFn := Array.push
    exportEntriesFn := .map Prod.fst
  }

/-- An attribute for defining motivated proof moves out of `InfoviewAction`s. -/
initialize registerBuiltinAttribute {
  name := `motivated_proof_move
  descr := "Declare a new motivated proof move to appear in the point-and-click tactic panel."
  applicationTime := .afterCompilation
  add := fun decl stx _ => do
    Attribute.Builtin.ensureNoArgs stx
    if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
    modifyEnv (infoviewActionExt.addEntry · (decl, ← mkInfoviewAction decl))
}

open scoped Jsx in
/-- Shortlist the applicable motivated proof moves and display them in a grid. -/
@[server_rpc_method]
def MotivatedProofPanel.rpc (props : InfoviewActionProps) : RequestM (RequestTask Html) := do
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
        fun (_, action) ↦ TermElabM.run' do
          Prod.fst <$> ( (action props).run { elaborator := .anonymous } 
                          |>.run { goals := [goal.mvarId] } )
      return .pure <|
        <details «open»={true}>
          <summary className="mv2 pointer">Motivated proof moves</summary>
          { .element "div" #[("class", "grid-container"), ("align", "center")] <|
              motivatedProofMoves.map (<div «class»={"grid-item"}>{·}</div>) }
        </details>

/-- The React component for the motivated proof panel. -/
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

/-- The syntax for the `motivated_proof` mode. 
    Typing this brings up the panel of motivated proof moves. -/
syntax (name := motivatedProofMode) "motivated_proof" tacticSeq : tactic

/-- The implementation of the `motivated_proof` tactic.
    This invokes the `MotivatedProofPanel` widget with the appropriate position data.
    The tactic state is converted into the tree representation in the process. -/
@[tactic motivatedProofMode] def motivatedProofModeImpl : Tactic
| stx@`(tactic| motivated_proof $seq) => do
  -- the start and end positions of the syntax block
  let some ⟨stxStart, stxEnd⟩ := (← getFileMap).rangeOfStx? stx | return ()
  -- the indentation of the `motivated_proof` block
  let indent := getBlockIndentation stx stxStart
  -- the position for the next tactic insertion
  let pos : Lsp.Position := { line := stxEnd.line + 1, character := indent }
  -- the range in the text document supplied to the motivated proof panel for tactic insertion
  -- the tactic is inserted at `stxEnd` rather than at `pos` to avoid complications when the block is at the end of the file
  -- the logic for handling the whitespace insertion is in `EditParams.ofReplaceWhitespace`
  -- this function is invoked by default in `DynamicEditButton`s with `onWhitespace` set to true
  let range : Lsp.Range := ⟨stxEnd, pos⟩
  -- save the widget for the motivated proof panel to the syntax `stx`
  Widget.savePanelWidgetInfo (hash MotivatedProofPanel.javascript) (stx := stx) do
    return json% { range : $(range) }
  -- this turns the goal into a tree initially
  Tree.workOnTreeDefEq pure
  -- evaluate the tactic sequence
  evalTacticSeq seq
|                 _                    => throwUnsupportedSyntax
where
  /--
  If `stx` is a tactic block of the form
  
  ```
  <main_tactic>
      <tac₁>
      <tac₂>
      ...
      ...
      ...
      <tacₙ>
  ```

  `getBlockIndentation` calculates the indentation of the tactic block
    `tac₁; tac₂; ...; tacₙ` (measured in terms of number of characters from the left margin).

  This is done by extracting the trailing `SourceInfo` of the `main_tactic`
  and calculating the length of its last line.

  If this fails, the indentation defaults to that of the `main_tactic` with an additional two spaces.

  The argument `start` is the start position of the `stx` syntax block in the editor.
  -/
  getBlockIndentation (stx : Syntax) (start : Lsp.Position) : Nat :=
    let indent? : Option Nat := do
      -- the leading and trailing whitespaces around the head of the syntax tree
      let (.original _leading _startPos trailing endPos) ← stx.getHeadInfo? | none
      -- this indirectly checks whether the tactic sequence is non-empty
      -- this case must be treated differently since it affects the trailing whitespace calculation 
      guard <| some endPos != stx.getTailPos?
      -- the lines in the trailing whitespace
      let trailingLines := trailing.toString |>.split (· = '\n')
      -- the last line of the trailing whitespace
      let lastLine ← trailingLines.getLast?
      -- the length of the last line
      return lastLine.length
    -- the indentation of the start of the full syntax block
    let stxIndent := start.character
    -- return the calculated indentation,
    -- defaulting to adding two spaces to the existing indentation if it is undefined
    indent?.getD (stxIndent + 2)

/-- A code action that offers to start a motivated proof within a tactic proof. -/
@[tactic_code_action *]
def startMotivatedProof : Std.CodeAction.TacticCodeAction :=
  fun _ _ _ stk node ↦ do
    let .node (.ofTacticInfo _) _ := node | return #[]
    let _ :: (seq, _) :: _ := stk | return #[]
    if seq.findStack? (·.isOfKind ``motivatedProofMode) (accept := fun _ ↦ true) |>.isSome then
      return #[] -- the cursor is already within a `motivated_proof` block in this situation
    let doc ← RequestM.readDoc
    let eager : Lsp.CodeAction := {
      title := "Start a motivated proof."
      kind? := "quickfix",
      isPreferred? := some .true
    }
    return #[{
      eager
      lazy? := some do
        let some ⟨seqStart, seqEnd⟩ := doc.meta.text.rangeOfStx? seq | return eager
        let indent := seqStart.character
        let ⟨edit, _⟩ := EditParams.ofReplaceWhitespace doc.meta 
          { start := seqEnd, «end» := { line := seqEnd.line + 1, character := indent } } 
          ("motivated_proof\n".pushn ' ' (indent + 2) )
        return { eager with
          edit? := some <| .ofTextDocumentEdit edit } }]

end MotivatedProofMode