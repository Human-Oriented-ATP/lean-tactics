import Lean.Server.Rpc.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Demos.Macro
import Std.Lean.Position
import Std.Util.TermUnsafe
import Std.CodeAction.Attr
import Mathlib
import Tree

namespace ProofWidgets
open Lean Server Elab Command Lsp

structure EditParams where
  edit : Lsp.TextDocumentEdit
  newCursorPos? : Option Lsp.Position := none
deriving RpcEncodable

/-- Replace `range` with `newText` and then place the cursor at the end of the new text. -/
def EditParams.ofReplaceRange (meta : Server.DocumentMeta) (range : Lsp.Range)
    (newText : String) : EditParams :=
  let edit := { textDocument := { uri := meta.uri, version? := meta.version }
                edits        := #[{ range, newText }] }
  let newCursorPos? := some {
    line := range.start.line
    character := range.start.character + newText.codepointPosToUtf16Pos newText.length
  }
  { edit, newCursorPos? }

def EditParams.insertLine (meta : Server.DocumentMeta) (line : Nat) 
    (indent : Nat) (text : String) : EditParams :=
  let newText := "".pushn ' ' indent ++ text
  let pos := { line := line, character := 0 }
  EditParams.ofReplaceRange meta ⟨pos, pos⟩ newText

structure DynamicButtonProps where
  label : String
  edit? : Option EditParams := none
  html? : Option Html := none
  vanish : Bool := false
  key   :=   label
deriving RpcEncodable

@[widget_module] def DynamicButton : Component DynamicButtonProps where
  javascript := include_str ".." / "build" / "js" / "dynamicButton.js"


structure DynamicEditButtonProps where
  label : String
  range? : Option Lsp.Range := none
  insertion? : Option String := none
  html? : Option Html := none
  vanish : Bool := false
deriving RpcEncodable

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
        vanish := props.vanish }

@[widget_module] def DynamicEditButton : Component DynamicEditButtonProps :=
  mk_rpc_widget% DynamicEditButton.rpc


section InfoviewAction

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
def MotivatedProofPanel.rpc (props : InfoviewActionProps) : RequestM (RequestTask Html) :=
  RequestM.withWaitFindSnapAtPos props.range.start fun snap ↦ do
    RequestM.runTermElabM snap do
      let props' := { props with range := ⟨props.range.end, props.range.end⟩ }
      let infoviewActions := infoviewActionExt.getState (← getEnv)
      let motivatedProofMoves ← infoviewActions.filterMapM 
        fun (_, action) ↦ (action props').run
      return .element "div" #[] motivatedProofMoves

@[widget_module] def MotivatedProofPanel : Component InfoviewActionProps :=
  mk_rpc_widget% MotivatedProofPanel.rpc

end InfoviewAction

section MotivatedProofMode

open Elab Tactic
open scoped Json

syntax (name := motivatedProofMode) "motivated_proof" tacticSeq : tactic

@[tactic motivatedProofMode] def motivatedProofModeImpl : Tactic
| stx@`(tactic| motivated_proof $seq) => do
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
    let newseq : TSyntax `Lean.Parser.Tactic.tacticSeq ← match seq with 
    | `(Parser.Tactic.tacticSeq| $[$tacs]*) => do
      let mkTree ← `(tactic| make_tree)
      let newTacs := (mkTree :: (List.intersperse mkTree) (tacs.toList)).toArray
      `(Parser.Tactic.tacticSeq | $[$newTacs]*)
    | _ => pure seq
    savePanelWidgetInfo stx ``MotivatedProofPanel do
      return json% { range : $(range) }
    evalTacticSeq newseq
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