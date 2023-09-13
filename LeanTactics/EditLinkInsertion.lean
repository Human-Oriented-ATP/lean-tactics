import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod
import Std.Lean.Position

open Lean Server ProofWidgets Elab Tactic Parser Tactic

syntax (name := motivatedProofMode) "motivated_proof" tacticSeq : tactic

macro "dummy" : tactic => `(tactic| skip)

open scoped ProofWidgets.Jsx ProofWidgets.Json

structure InsertionProps where
  text : String
  indent : String
  range : Lsp.Range
deriving RpcEncodable

def ProofWidgets.MakeEditLinkProps.ofReplaceRange' (meta : Server.DocumentMeta) (range : Lsp.Range)
    (indent : String) (newText : String) : MakeEditLinkProps :=
  let edit := { textDocument := { uri := meta.uri, version? := meta.version }
                edits        := #[{ range, newText }] }
  let newCursorPos? := some {
    line := range.end.line + 1
    character := indent.codepointPosToUtf16Pos indent.length
  }
  { edit, newCursorPos? }

open scoped Jsx in
@[server_rpc_method]
def Insertion.rpc (props : InsertionProps) : RequestM (RequestTask Html) := do
  RequestM.asTask do
    let doc ← RequestM.readDoc
    return .ofComponent MakeEditLink (children := #[ .text "Add tactic" ]) <| .ofReplaceRange'
      doc.meta
      props.range
      props.indent
      props.text

@[widget_module]
def InsertionComponent : Component InsertionProps :=
  mk_rpc_widget% Insertion.rpc

@[tactic motivatedProofMode]
def motivatedProofImpl : Tactic
  | stx@`(tactic| motivated_proof $tacs) => do
    let fileMap ← getFileMap
    let some stxRange := fileMap.rangeOfStx? stx | return
    let indent : String :=
      match stx.getHeadInfo with
        | .original _ _ trailing _ => trailing.toString
        |           _              => panic! "Bad SourceInfo"
    let txt := stx.reprint.get!.trimRight ++ indent ++ "dummy"
    savePanelWidgetInfo stx ``InsertionComponent do
      return json% { text: $(txt), indent: $(indent), range: $(stxRange) }
    evalTactic tacs
  | _ => throwUnsupportedSyntax

example : ∀ n : ℕ, 1 = 1 := by
  motivated_proof
    intro _
    sorry
    dummy
    dummy
    dummy
