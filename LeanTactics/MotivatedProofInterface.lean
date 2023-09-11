import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Panel
import RewriteExperiments
import RewriteOrd
import SelectInsertPanel
import Aesop
import TreeApply
import TreeRewrite
import Mathlib.Data.SetLike.Basic
import ProofWidgets.Component.SelectionPanel

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


def insertRewriteAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (goals_ : goalLocation) : MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something"
  let some pos2 := subexprPos[1]? | throwError "You must select something"
  let .hyp hypFvarId := pos2.loc | throwError "You need to select a hypothesis"
  let hypName := LocalContext.get! (← getLCtx) hypFvarId
  let ⟨_, .target subexprPos1⟩ := pos1 | throwError "You need to select a hypothesis"
  return "rewriteAt " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " [" ++ (hypName.userName.toString) ++ "]"

def insertRewriteAt' (subexprPos : Array (WithRpcRef Elab.ContextInfo × SubExpr.GoalsLocation)) : MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something"
  let some pos2 := subexprPos[1]? | throwError "You must select something"
  let .hyp hypFvarId := pos2.2.loc | throwError "You need to select a hypothesis"
  let hypName := LocalContext.get! (← getLCtx) hypFvarId
  let ⟨_, .target subexprPos1⟩ := pos1.2 | throwError "You need to select a hypothesis"
  return "rewriteAt " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " [" ++ (hypName.userName.toString) ++ "]"


mkSelectInsertTacticTwo "rewriteAt?" "rewriteAt 🔍"
    "Use shift-click to select one sub-expression in the goal that you want to zoom on."     
    insertRewriteAt

def insertRewriteOrdAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (_goalLoc : goalLocation) : MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something."
  let some pos2 := subexprPos[1]? | throwError "You must select something."
  let .hyp hypFvarId := pos2.loc | throwError "You need to select a hypothesis"
  let hypName := LocalContext.get! (← getLCtx) hypFvarId
  let ⟨_, .target subexprPos1⟩   := pos1 | throwError "You must select something in the goal."
  return "rewriteOrdAt " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " [" ++ (hypName.userName.toString) ++ "]"

def insertRewriteOrdAt' (subexprPos : Array (WithRpcRef Elab.ContextInfo × SubExpr.GoalsLocation)) : MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something."
  let some pos2 := subexprPos[1]? | throwError "You must select something."
  let .hyp hypFvarId := pos2.2.loc | throwError "You need to select a hypothesis"
  let hypName := LocalContext.get! (← getLCtx) hypFvarId
  let ⟨_, .target subexprPos1⟩   := pos1.2 | throwError "You must select something in the goal."
  return "rewriteOrdAt " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " [" ++ (hypName.userName.toString) ++ "]"

mkSelectInsertTacticTwo "rewriteOrdAt?" "rewriteOrdAt 🔍"
  "Use shift-click to select one sub-expression in the goal that you want to zoom on."
  insertRewriteOrdAt

def insertTreeApplyAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (goals_ : goalLocation): MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something."
  let some pos2 := subexprPos[1]? | throwError "You must select something."
  let ⟨_, .target subexprPos1⟩   := pos1 | throwError "You must select something in the goal."
  let ⟨_, .target subexprPos2⟩ := pos2 | throwError "You must select something in the goal."
  return ("tree_apply " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ ((SubExpr.Pos.toArray subexprPos2).toList).toString)

def insertTreeApplyAt' (subexprPos : Array (WithRpcRef Elab.ContextInfo × SubExpr.GoalsLocation)) : MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something."
  let some pos2 := subexprPos[1]? | throwError "You must select something."
  let ⟨_, .target subexprPos1⟩   := pos1.2 | throwError "You must select something in the goal."
  let ⟨_, .target subexprPos2⟩ := pos2.2 | throwError "You must select something in the goal."
  return ("tree_apply " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ ((SubExpr.Pos.toArray subexprPos2).toList).toString)

mkSelectInsertTacticTwo "TreeApply?" "TreeApply 🔍"
      "Use shift-click to select two sub-expression in the goal that you want to zoom on."
      insertTreeApplyAt

def insertTreeRewriteAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (goals_ : goalLocation): MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something."
  let some pos2 := subexprPos[1]? | throwError "You must select something."
  let ⟨_, .target subexprPos1⟩   := pos1 | throwError "You must select something in the goal."
  let ⟨_, .target subexprPos2⟩ := pos2 | throwError "You must select something in the goal."
  return ("tree_rewrite " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ ((SubExpr.Pos.toArray subexprPos2).toList).toString)

def insertTreeRewriteAt' (subexprPos : Array (WithRpcRef Elab.ContextInfo × SubExpr.GoalsLocation)) : MetaM String := do
  let some pos1 := subexprPos[0]? | throwError "You must select something."
  let some pos2 := subexprPos[1]? | throwError "You must select something."
  let ⟨_, .target subexprPos1⟩   := pos1.2 | throwError "You must select something in the goal."
  let ⟨_, .target subexprPos2⟩ := pos2.2 | throwError "You must select something in the goal."
  return ("tree_rewrite " ++ ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ ((SubExpr.Pos.toArray subexprPos2).toList).toString)

mkSelectInsertTacticTwo "TreeRewrite?" "TreeRewrite 🔍"
      "Use shift-click to select two sub-expression in the goal that you want to zoom on."
      insertTreeRewriteAt

section TextInsertion

structure InsertionCommandProps where
  pos : Lsp.Position
  text : String
deriving RpcEncodable

structure InsertionCommandPropsWithCtx extends InsertionCommandProps where
  locations : Array (WithRpcRef Elab.ContextInfo × SubExpr.GoalsLocation)
deriving RpcEncodable

structure InsertionButton where
  label : String
  text : String
  num : Nat
deriving RpcEncodable

structure InsertionResponse where
  edit : Lsp.WorkspaceEdit
  newPos : Lsp.Position
deriving RpcEncodable

def insertTextWithCtx (pos : Lsp.Position) (stx : Syntax) (msg : String) (selectedLocations : Array (WithRpcRef Elab.ContextInfo × SubExpr.GoalsLocation)) (doc : FileWorker.EditableDocument) :
    RequestM InsertionResponse := do
  let filemap := doc.meta.text
  let .some tailPos := stx.getTailPos? | IO.throwServerError "Unable to retrieve syntax tail position."
  let lspTailPos := max pos (filemap.utf8PosToLspPos tailPos)
  let indentation := stx.getIndentation
  -- let msg ← if msg == "rewriteOrdAt?" then 
  --   let some loc2 := selectedLocations[0]? | IO.throwServerError "No two locations selected"
  --   (Lean.Elab.ContextInfo.runMetaM loc2.1.val {} (insertRewriteOrdAt' selectedLocations)) else pure msg
  -- let msg ← if msg == "rewriteAt? " then
  --   let some loc := selectedLocations[0]? | IO.throwServerError "No two locations selected" 
  --   (Lean.Elab.ContextInfo.runMetaM loc.1.val {} (insertRewriteAt' selectedLocations)) else pure msg
  let msg ← if msg == "TreeApply? " then 
    let some loc1 := selectedLocations[0]? | IO.throwServerError "No locations selected"
    (Lean.Elab.ContextInfo.runMetaM loc1.1.val {} (insertTreeApplyAt' selectedLocations)) else pure msg
  let msg ← if msg == "TreeRewrite? " then 
    let some loc1 := selectedLocations[0]? | IO.throwServerError "No locations selected"
    (Lean.Elab.ContextInfo.runMetaM loc1.1.val {} (insertTreeRewriteAt' selectedLocations)) else pure msg
  let textEdit : Lsp.TextEdit :=
    { range := { start := lspTailPos, «end» := lspTailPos },
      newText := "\n".pushn ' ' indentation ++ msg }
  let textDocumentEdit : Lsp.TextDocumentEdit :=
    { textDocument := { uri := doc.meta.uri, version? := doc.meta.version },
      edits := #[textEdit] }
  let edit := Lsp.WorkspaceEdit.ofTextDocumentEdit textDocumentEdit
  return { edit := edit, newPos := ⟨lspTailPos.line + 1, indentation + msg.length⟩ }

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
def makeInsertionCommandWithCtx : InsertionCommandPropsWithCtx → RequestM (RequestTask InsertionResponse)
  | ⟨props, locations⟩ =>
    RequestM.withWaitFindSnapAtPos props.pos fun snap ↦ do
      let doc ← RequestM.readDoc
      insertTextWithCtx props.pos snap.stx props.text locations doc

@[server_rpc_method]
def makeInsertionCommand : InsertionCommandProps → RequestM (RequestTask InsertionResponse)
  | ⟨pos, text⟩ =>
    RequestM.withWaitFindSnapAtPos pos fun snap ↦ do
      let doc ← RequestM.readDoc
      insertText pos snap.stx text doc

end TextInsertion

namespace MotivatedProofInterface

macro "◾" label:str " → " tac:tactic "{" num:num "}":term =>
  let text : StrLit := Syntax.mkStrLit tac.raw.reprint.get!
 `(term| InsertionButton.mk $label $text $num)

end MotivatedProofInterface

/-- The buttons that appear as proof-generating moves in the infoview panel. -/
def tacticButtons : Array InsertionButton :=
  #[ ◾ "Introduce a variable into the context" →  try (intro x) {0}, -- need to think about how to handle variable names
     ◾       "Use function extensionality"     →  try (apply funext) {0},
     ◾           "Insert a sorry"              →  sorry {0},
     ◾         "Simplify the target"           →  simp {0},
     ◾  "Apply to Tree"                        →  TreeApply? {2},
     ◾  "Attempt to close the goal with Aesop" →  aesop {0},
     ◾  "Turn the tactic state into a Tree"    →  make_tree {0},
     ◾  "Targetted ordered rewrite"            →  rewriteOrdAt? {2},
     ◾  "Targetted rewrite"            →  rewriteAt? {2},
     ◾  "Tree Rewrite"            →  TreeRewrite? {2}]

namespace MotivatedProofInterface

open ProofWidgets
open scoped Json Jsx

opaque MotivatedProofPanelProps : Type
-- deriving RpcEncodable

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

-- `tree apply` example
example {p q r : Prop}: (p → q) → (q → r) → (p → r) := by
motivated_proof
    make_tree 
    tree_apply [0, 1, 1] [1, 0, 1, 0, 1]
    tree_apply [0, 1, 1] [1, 1]
    tree_apply [0, 1] [1]

example {p q r : Prop} (h : p = q): (p → q) := by 
motivated_proof
  rewriteAt [0] [h] 
  sorry

--`tree rewrite + apply` example
example {p q : Prop} : p = q → (p → q) := by 
motivated_proof
  make_tree
  tree_rewrite [0, 1] [1, 0, 1]
  tree_apply [0, 1] [1]
  
-- `ordered rewrite` example
example {m n : Nat} (h : m ≤ n) : m ≤ 2 * n := by 
motivated_proof
  rewriteOrdAt [0, 1] [h]
  sorry


/- `TODO`: Fix placing of inserted tactic blocks as on repeated clicks the 
    insertion appears too high up the block. Currently have to click on and off. -/