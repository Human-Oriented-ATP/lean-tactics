import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Panel

open Lean Server

section Utils

def Lean.Syntax.contains? (pos : String.Pos) (stx : Syntax) : Bool := Option.toBool do
  let ⟨start, stop⟩ ← stx.getRange?
  guard <| start ≤ pos
  guard <| pos ≤ stop

def Lean.Syntax.Stack.findSmallest? (stack : Syntax.Stack) (p : Syntax → Bool) : Option Syntax :=
  stack |>.map Prod.fst |>.filter p |>.head?

def Lean.Syntax.getHeadKind? (stx : Syntax) :=
  Syntax.getKind <$> stx.getHead?

def String.getLastLine! (text : String) : String :=
  text |>.trim |>.splitOn "\n" |>.getLast!

def String.getLineIndentation (line : String) : Nat :=
  line |>.takeWhile (· ∈ [' ', '·', '{', '}']) |>.length

def Lean.Syntax.getIndentation (stx : Syntax) : Nat :=
  stx |>.reprint.get! |>.getLastLine! |>.getLineIndentation

instance [LE α] [DecidableRel (LE.le (α := α))] : Max α where
  max x y := if x ≤ y then y else x

end Utils

section TextInsertion

structure InsertionCommandProps where
  pos : Lsp.Position
  text : String
deriving RpcEncodable

structure InsertionButton where
  label : String
  text : String
deriving RpcEncodable

structure InsertionResponse where
  edit : Lsp.WorkspaceEdit
  newPos : Lsp.Position
deriving RpcEncodable

def insertText (pos : Lsp.Position) (stx : Syntax) (msg : String) (doc : FileWorker.EditableDocument) :
    RequestM InsertionResponse := do
  let filemap := doc.meta.text
  let .some tailPos := stx.getTailPos? | IO.throwServerError "Unable to retrieve syntax tail position."
  let lspTailPos := max pos (filemap.utf8PosToLspPos tailPos)
  let indentation := stx.getIndentation
  let textEdit : Lsp.TextEdit :=
    { range := { start := lspTailPos, «end» := lspTailPos },
      newText := "\n".pushn ' ' indentation ++ msg }
  let textDocumentEdit : Lsp.TextDocumentEdit :=
    { textDocument := { uri := doc.meta.uri, version? := doc.meta.version },
      edits := #[textEdit] }
  let edit := Lsp.WorkspaceEdit.ofTextDocumentEdit textDocumentEdit
  return { edit := edit, newPos := ⟨lspTailPos.line + 1, indentation⟩ }

@[server_rpc_method]
def makeInsertionCommand : InsertionCommandProps → RequestM (RequestTask InsertionResponse)
  | ⟨pos, text⟩ =>
    RequestM.withWaitFindSnapAtPos pos fun snap ↦ do
      let doc ← RequestM.readDoc
      insertText pos snap.stx text doc

end TextInsertion

namespace MotivatedProofInterface

macro "◾" label:str " → " tac:tactic : term =>
  let text : StrLit := Syntax.mkStrLit tac.raw.reprint.get!
 `(term| InsertionButton.mk $label $text)

end MotivatedProofInterface

/-- The buttons that appear as proof-generating moves in the infoview panel. -/
def tacticButtons : Array InsertionButton :=
  #[ ◾ "Introduce variables into the context"  →  try (intros),
     ◾       "Use function extensionality"     →  try (apply funext),
     ◾           "Insert a sorry"              →  sorry,
     ◾         "Simplify the target"           →  simp ]

namespace MotivatedProofInterface

open ProofWidgets
open scoped Json Jsx

structure MotivatedProofPanelProps where
  pos : Lsp.Position
  buttons : Array InsertionButton
deriving RpcEncodable

@[widget_module]
def MotivatedProofPanel : Component MotivatedProofPanelProps where
  javascript := include_str "../build/js/motivatedProofUI.js"

syntax (name := motivatedProofMode) "motivated_proof" tacticSeq : tactic

open Lean Elab Tactic in
@[tactic motivatedProofMode]
def motivatedProofImpl : Tactic
  | stx@`(tactic| motivated_proof $tacs) => do
    savePanelWidgetInfo stx ``MotivatedProofPanel do
      return json% { buttons : $(← rpcEncode tacticButtons) }
    evalTacticSeq tacs
  | _ => throwUnsupportedSyntax

end MotivatedProofInterface


example : 1 = 1 := by
  motivated_proof
    sorry
