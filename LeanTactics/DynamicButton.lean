import Lean.Server.Rpc.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay

namespace ProofWidgets
open Lean Server Elab

structure EditParams where
  edit : Lsp.TextDocumentEdit
  newCursorPos? : Option Lsp.Position := none

/-- Replace `range` with `newText` and then place the cursor at the end of the new text. -/
def EditProps.ofReplaceRange (meta : Server.DocumentMeta) (range : Lsp.Range)
    (newText : String) : EditParams :=
  let edit := { textDocument := { uri := meta.uri, version? := meta.version }
                edits        := #[{ range, newText }] }
  let newCursorPos? := some {
    line := range.start.line
    character := range.start.character + newText.codepointPosToUtf16Pos newText.length
  }
  { edit, newCursorPos? }

def EditProps.insertLine (meta : Server.DocumentMeta) (line : Nat) 
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
  html : Option Html := none

#mkrpcenc DynamicButtonProps

@[widget_module] def DynamicButton : Component DynamicButtonProps where
  javascript := include_str "../build/js/dynamicButton.js"

