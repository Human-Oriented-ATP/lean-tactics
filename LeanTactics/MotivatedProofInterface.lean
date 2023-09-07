import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Panel
import RewriteExperiments
import RewriteOrd
import SelectInsertPanel
import Aesop
import TreeApply
import Mathlib.Data.SetLike.Basic

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
  return { edit := edit, newPos := ⟨lspTailPos.line + 1, indentation + msg.length⟩ }

@[server_rpc_method]
def makeInsertionCommand : InsertionCommandProps → RequestM (RequestTask InsertionResponse)
  | ⟨pos, text⟩ =>
    RequestM.withWaitFindSnapAtPos pos fun snap ↦ do
      let doc ← RequestM.readDoc
      insertText pos snap.stx text doc

end TextInsertion

def insertRewriteAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) : MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something."
  let some pos2 := subexprPos[1]? | throwError "You must select something"
  let .hyp hypFvarId := pos2.loc | throwError "You need to select a hypothesis"
  let hypName := LocalContext.get! (← getLCtx) hypFvarId
  let ⟨_, .target subexprPos1⟩ := pos1 | throwError "You must select something in the goal."
  return "rewriteAt " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " [" ++ (hypName.userName.toString) ++ "]"

mkSelectInsertTacticTwo "rewriteAt?" "rewriteAt 🔍"
    "Use shift-click to select one sub-expression in the goal that you want to zoom on."
    insertRewriteAt

def insertRewriteOrdAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) : MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something."
  let some pos2 := subexprPos[1]? | throwError "You must select something."
  let .hyp hypFvarId := pos2.loc | throwError "You need to select a hypothesis"
  let hypName := LocalContext.get! (← getLCtx) hypFvarId
  let ⟨_, .target subexprPos1⟩ := pos1 | throwError "You must select something in the goal."
  return "rewriteOrdAt " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " [" ++ (hypName.userName.toString) ++ "]"

mkSelectInsertTacticTwo "rewriteOrdAt?" "rewriteOrdAt 🔍"
    "Use shift-click to select one sub-expression in the goal that you want to zoom on."
    insertRewriteOrdAt

def insertTreeApplyAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) : MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something."
  let some pos2 := subexprPos[1]? | throwError "You must select something."
  let ⟨_, .target subexprPos1⟩ := pos1 | throwError "You must select something in the goal."
  let ⟨_, .target subexprPos2⟩ := pos2 | throwError "You must select something in the goal."
  return ("tree_apply " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ ((SubExpr.Pos.toArray subexprPos2).toList).toString)

mkSelectInsertTacticTwo "TreeApply?" "TreeApply 🔍"
    "Use shift-click to select two sub-expression in the goal that you want to zoom on."
    insertTreeApplyAt

namespace MotivatedProofInterface

macro "◾" label:str " → " tac:tactic : term =>
  let text : StrLit := Syntax.mkStrLit tac.raw.reprint.get!
 `(term| InsertionButton.mk $label $text)

end MotivatedProofInterface

/-- The buttons that appear as proof-generating moves in the infoview panel. -/
def tacticButtons : Array InsertionButton :=
  #[ ◾ "Introduce a variable into the context" →  try (intro x), -- need to think about how to handle variable names
     ◾       "Use function extensionality"     →  try (apply funext),
     ◾           "Insert a sorry"              →  sorry,
     ◾         "Simplify the target"           →  simp,
     ◾         "Targetted rewrite"             →  rewriteAt?,
     ◾         "Targetted ordered rewrite"     →  rewriteOrdAt?,
     ◾  "Attempt to close the goal with Aesop" →  aesop,
     ◾  "Turn the tactic state into a Tree"    →  make_tree,
     ◾  "Apply to Tree"                        →  TreeApply?]

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


--more elaborate example
example : (fun x : Nat => x) = (id : Nat → Nat) := by
  motivated_proof
    try (apply funext)
    try (intros)
    simp

example (h : p = q) : p → q := by
  motivated_proof
    rewriteAt [0] [h]
    aesop

example {a b c : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ c) : a ⊆ c := by
  motivated_proof
    try (intro x)
    rewriteOrdAt [0, 1] [h₁]
    rewriteOrdAt [0, 1] [h₂]
    make_tree
    tree_apply [0, 1] [1]

example {a b c : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ c) : a ⊆ c := by 
motivated_proof
    rewriteOrdAt?
    rewriteOrdAt [0, 1] [h₁]
  


/- `TODO`: Fix placing of inserted tactic blocks as on repeated clicks the 
    insertion appears too high up the block. Currently have to click on and off. -/

