import Lean
import LeanTactics.EditLinkInsertion
import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod
import Std.Lean.Position
import ProofWidgets
import Std

open Lean Server ProofWidgets Elab Tactic Parser Tactic ProofWidgets

open scoped ProofWidgets.Jsx ProofWidgets.Json

/-- Structure for rendering Grids with Buttons -/
structure GridProps where
  direction : String
  spacing : Nat
deriving RpcEncodable

/-- Structure for rendering Typography objects with Buttons -/
structure TypographyProps where
  variant : String
  display : String
  mt : Nat -- stands for margin top
deriving RpcEncodable

/-- Structure for rendering the display Button objects with Buttons -/
structure DisplayButtonProps where
  variant : String
  color : String
  size : String
  container : Bool
  item : Bool
deriving RpcEncodable

structure ButtonPropsBundle where
  gridProps : GridProps
  typoProps : TypographyProps
  displayButtonProps : DisplayButtonProps
deriving RpcEncodable

structure Button where
  title : String
  editText : String
  newDisplay : Option (HtmlDisplayProps)
  buttonPropsBundle : ButtonPropsBundle
deriving RpcEncodable

structure ButtonsPanel where 
  Buttons : List Button
  panelProps : PanelWidgetProps

def DisplayButtonProps.default : DisplayButtonProps := ⟨"outlined", "primary", "medium", Bool.false, Bool.false⟩

def TypographyProps.default : TypographyProps := ⟨"button", "block", 2⟩

def GridProps.default : GridProps := ⟨"column", 2⟩

def ButtonPropsBundle.default : ButtonPropsBundle := ⟨.default, .default, .default⟩ 

def Button.insert_default (title : String) (editText : String) : Button := ⟨title, editText, none, .default⟩

def emptyEdit (meta : Server.DocumentMeta) (range : Lsp.Range) :  MakeEditLinkProps := 
  MakeEditLinkProps.ofReplaceRange meta range ""

def AllButtons : List Button := [ (Button.insert_default "try simp" "dummy"), (Button.insert_default "try simp" "dummy") ]

structure MakeEditButtonLinkProps extends MakeEditLinkProps where
  buttonProps : ButtonPropsBundle
deriving RpcEncodable

structure MakeEditButtonsLinkProps extends PanelWidgetProps where
  buttonProps : Array MakeEditButtonLinkProps
deriving RpcEncodable

/-- A link that, when clicked, makes the specifies edit and potentially moves the cursor. -/
@[widget_module]
def MakeEditButtonsLink : Component MakeEditButtonsLinkProps where
  javascript := include_str ".." / "build" / "js" / "makeEditButton.js"


syntax (name := motivatedProofMode') "motivated_proof'" tacticSeq : tactic

macro "dummy1" : tactic => `(tactic| skip)

def ProofWidgets.MakeEditButtonLinkProps.ofReplaceRange (meta : Server.DocumentMeta) (range : Lsp.Range)
    (indent : String) (buttons : List Button) : Array MakeEditButtonLinkProps := Id.run do
  let newCursorPos : Option Lsp.Position := some {
      line := range.end.line + 1
      character := indent.codepointPosToUtf16Pos indent.length
    }
  let newPos : Lsp.Position := {
      line := range.end.line + 1
      character := indent.codepointPosToUtf16Pos indent.length
    }
  let newRange : Lsp.Range := {start := newPos, «end» := newPos }
  let mut props : List MakeEditButtonLinkProps := []
  for button in buttons do
    let edit : Lsp.TextDocumentEdit := ⟨{ uri := meta.uri, version? := meta.version }, #[{ range := newRange, newText := button.editText}]⟩
    let newprops : MakeEditButtonLinkProps := {buttonProps := button.buttonPropsBundle, edit := edit, newCursorPos? := newCursorPos, title? := button.title}
    props := props.concat newprops
  return props.toArray

structure InsertionPropsButton extends PanelWidgetProps where
  indent : String
  range : Lsp.Range
deriving RpcEncodable

open scoped Jsx in
@[server_rpc_method]
def Insertion.rpc' (props : InsertionPropsButton) : RequestM (RequestTask Html) := do
  RequestM.asTask do
    let doc ← RequestM.readDoc
    return .ofComponent MakeEditButtonsLink (children := #[]) <| 
    { pos := props.pos
      goals := props.goals
      termGoal? := props.termGoal?
      selectedLocations := props.selectedLocations
      buttonProps := ProofWidgets.MakeEditButtonLinkProps.ofReplaceRange doc.meta props.range props.indent AllButtons
    }

@[widget_module]
def InsertionComponent' : Component InsertionPropsButton :=
  mk_rpc_widget% Insertion.rpc'

@[tactic motivatedProofMode']
def motivatedProof'Impl : Tactic
  | stx@`(tactic| motivated_proof' $tacs) => do
    let fileMap ← getFileMap
    let some stxRange := fileMap.utf8RangeToLspRange <$> stx.getRange? | return
    let indent : String :=
      match stx.getHeadInfo with
        | .original _ _ trailing _ => trailing.toString
        |           _              => panic! "Bad SourceInfo"
    savePanelWidgetInfo stx ``InsertionComponent' do
      return json% { indent: $(indent), range: $(stxRange)}
    evalTactic tacs
  | _ => throwUnsupportedSyntax


/-
~Mantas: Note that some fields that are called on the JavaScript side are not stored here, as we will always
want to access their default values (such as `gutterBottom` or `container`)
Additionally, the insert functionality still forgets about the correct indentation (still need to `fix`)
-/

example : (1 : Nat) = 1 := by
motivated_proof'
dummy

/- -/
