import Lean.Server.Rpc.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod

namespace ProofWidgets
open Lean Server Elab

structure EditParams where
  edit : Lsp.TextDocumentEdit
  newCursorPos? : Option Lsp.Position := none

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

structure DynamicButtonProps extends EditParams where
  label : String
  html? : Option Html := none
deriving RpcEncodable

@[widget_module] def DynamicButton : Component DynamicButtonProps where
  javascript := include_str "../build/js/dynamicButton.js"


structure DynamicEditButtonProps where
  label : String
  range : Lsp.Range
  insertion : String
  html? : Option Html := none
deriving RpcEncodable

@[server_rpc_method]
def DynamicEditButton.rpc (props : DynamicEditButtonProps) : RequestM (RequestTask Html) := do
  RequestM.asTask do
    let doc ← RequestM.readDoc
    let editParams := EditParams.ofReplaceRange doc.meta props.range props.insertion
    return .ofComponent DynamicButton (children := #[])
      { editParams with
        label := props.label
        html? := props.html? }

@[widget_module] def DynamicEditButton : Component DynamicEditButtonProps :=
  mk_rpc_widget% DynamicEditButton.rpc