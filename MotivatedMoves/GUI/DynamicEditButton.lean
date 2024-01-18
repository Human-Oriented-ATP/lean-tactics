import ProofWidgets

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

/-- Add `newText` with correct indentation at the end of `range`, which is assumed to be entirely whitespace. -/
def ofReplaceWhitespace (meta : Server.DocumentMeta) (range : Lsp.Range)
    (newText : String) : EditParams :=
  let newLines := range.end.line - range.start.line
  let indent := range.end.character
  let newPaddedText := "" |>.pushn '\n' newLines |>.pushn ' ' indent |>.append newText
  let edit := { textDocument := { uri := meta.uri, version? := meta.version }
                edits        := #[{ range := ⟨range.start, range.start⟩, newText := newPaddedText }] }
  let newCursorPos? := some {
    line := range.end.line
    character := range.end.character + newText.codepointPosToUtf16Pos newText.length
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
deriving RpcEncodable

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
  javascript := include_str ".." / ".." / "build" / "js" / "dynamicButton.js"

/-- A wrapper around `DynamicButton` that requires an `Lsp.Range` instead of `EditParams`.
    This is usually much more convenient in practice. -/
structure DynamicEditButtonProps extends DynamicButtonStylingProps where
  label : String
  range? : Option Lsp.Range := none
  insertion? : Option String := none
  html? : Option Html := none
  onWhitespace : Bool := true
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
      if props.onWhitespace then
        return .ofReplaceWhitespace doc.meta range insertion
      else
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
