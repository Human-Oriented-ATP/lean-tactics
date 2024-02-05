import ProofWidgets
import Std.Lean.Position

open Lean Server Elab Command Lsp

namespace Rubik

end Rubik

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

structure InsertButtonProps where
  icon : String
  color : String
  edit : EditParams
  key := icon++color  -- this is needed for technical reasons to do with rendering React components
deriving RpcEncodable

open ProofWidgets

@[widget_module]
def InsertButton : Component InsertButtonProps where
  javascript := include_str ".." / ".." / "build" / "js" / "insertButton.js"

structure InsertEditButtonProps where
  icon : String
  color : String
  range : Lsp.Range
  insertion : String
  onWhitespace : Bool := true
deriving RpcEncodable

/-- The logic for generating a `DynamicButton` from the `DynamicEditButtonParams`. -/
@[server_rpc_method]
def InsertEditButton.rpc (props : InsertEditButtonProps) : RequestM (RequestTask Html) := do
  RequestM.asTask do
    let doc ← RequestM.readDoc
    let editParams : EditParams :=
      let range := props.range
      let insertion := props.insertion
      if props.onWhitespace then
        .ofReplaceWhitespace doc.meta range insertion
      else
        .ofReplaceRange doc.meta range insertion
    return .ofComponent InsertButton (children := #[])
      { icon := props.icon
        color := props.color
        edit := editParams }

@[widget_module] def InsertEditButton : Component InsertEditButtonProps :=
  mk_rpc_widget% InsertEditButton.rpc

open scoped Jsx Json

#check Lsp.Range

elab stx:"#insert_test " icon:str col:str s:str : command => liftTermElabM do
  let text:String := s.getString
  let some range := (←getFileMap).rangeOfStx? stx | return
  -- let range : Lsp.Range := {start := ⟨131,8⟩, «end» := ⟨131,13⟩}
  Widget.savePanelWidgetInfo (hash InsertEditButton.javascript) (return json%{
    icon : $(icon.getString),
    color : $(col.getString),
    range : $(range),
    insertion : $(text),
    onWhitespace : $(false)
  } ) stx

open Lean Parser Tactic Elab

syntax (name:=whatever) "with_insert_button" tacticSeq : tactic

@[tactic whatever]
def whateverImpl:Tactic
| stx@`(tactic|with_insert_button $seq) => do
  let some ⟨_, stxEnd⟩ := (←getFileMap).rangeOfStx? stx | return
  -- the leading and trailing whitespaces around the `motivated_proof` syntax node
  let some (.original leading _ trailing _) := stx.getHeadInfo? | panic! s!"Could not extract head information from {stx}."
  let extractIndentation (s : Substring) : Nat :=
    s.toString |>.split (· = '\n') |>.getLast! |>.length -- compute the indentation of the last line in the string
  let indent : Nat := -- compute the appropriate indentation for the next tactic
    extractIndentation trailing
  let pos : Lsp.Position := { line := stxEnd.line + 1, character := indent }
  let range : Lsp.Range := ⟨stxEnd, pos⟩
  let display_trailing := trailing.toString |>.replace " " "-" |>.replace "\n" "+"
  -- dbg_trace s!"{range.start.line} {range.start.character} {range.end.line} {range.end.character}"
  Widget.savePanelWidgetInfo (hash InsertEditButton.javascript) (return json%{
    icon : $(s!"Insert simp at {range.start.line} {range.start.character} {range.end.line} {range.end.character} {display_trailing}"),
    range : $(range),
    insertion : $("simp"),
    onWhitespace : $(true)
  } ) stx
| _ => throwUnsupportedSyntax

#insert_test "cw" "dodgerblue" "hello"
#insert_test "cw" "red" "hello"
#insert_test "cw" "snow" "hello"
#insert_test "cw" "yellow" "hello"
#insert_test "cw" "orange" "hello"
#insert_test "cw" "green" "hello"
#insert_test "ccw" "dodgerblue" "hello"
#insert_test "ccw" "red" "hello"
#insert_test "ccw" "snow" "hello"
#insert_test "ccw" "yellow" "hello"
#insert_test "ccw" "orange" "hello"
#insert_test "ccw" "green" "hello"
