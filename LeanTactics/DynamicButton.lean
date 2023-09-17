import Lean.Server.Rpc.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Demos.Macro
import Std.Lean.Position
import Std.Util.TermUnsafe

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
  let pos : Lsp.Position := { line := line, character := 0 }
  let edit := { textDocument := { uri := meta.uri, version? := meta.version },
                edits := #[⟨⟨pos, pos⟩, newText, none⟩] }
  let newCursorPos? := some {
    line := line,
    character := newText.codepointPosToUtf16Pos newText.length
  }
  ⟨edit, newCursorPos?⟩ 

structure DynamicButtonProps where
  label : String
  edit? : Option EditParams := none
  html? : Option Html := none
deriving RpcEncodable

@[widget_module] def DynamicButton : Component DynamicButtonProps where
  javascript := include_str "../build/js/dynamicButton.js"


structure DynamicEditButtonProps where
  label : String
  range? : Option Lsp.Range := none
  insertion? : Option String := none
  html? : Option Html := none
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
        html? := props.html? }

@[widget_module] def DynamicEditButton : Component DynamicEditButtonProps :=
  mk_rpc_widget% DynamicEditButton.rpc


section InfoviewAction

structure InfoviewActionProps extends PanelWidgetProps where
  range : Lsp.Range
deriving RpcEncodable

abbrev InfoviewAction := InfoviewActionProps → MetaM (Option Html)

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
  add := fun decl stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == AttributeKind.global do
      throwError "invalid attribute 'motivated_proof_move', must be global"
    if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
    modifyEnv (infoviewActionExt.addEntry · (decl, ← mkInfoviewAction decl))
}

end InfoviewAction