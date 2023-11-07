import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod
import Lean
import Std.Lean.Position

open Lean Elab Tactic Server ProofWidgets

open scoped ProofWidgets.Jsx ProofWidgets.Json

macro "dummy" : tactic => `(tactic| skip)

structure InsertionProps where
  range : Lsp.Range
  text : String
deriving RpcEncodable

def ProofWidgets.MakeEditLinkProps.ofReplaceRange' (meta : Server.DocumentMeta) (range : Lsp.Range)
    (newText : String) : MakeEditLinkProps :=
  let edit := { textDocument := { uri := meta.uri, version? := meta.version }
                edits        := #[{ range, newText }] }
  let splitText := newText.split (· = '\n')
  let lastText := splitText.getLast!
  let newCursorPos? := some {
    line := range.start.line + splitText.length - 1
    character := lastText.codepointPosToUtf16Pos lastText.length
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
      props.text

@[widget_module]
def InsertionComponent : Component InsertionProps :=
  mk_rpc_widget% Insertion.rpc

syntax (name := testProofSeq) "test_proof_seq" str tacticSeq : tactic

@[tactic testProofSeq]
def testProofSeqImpl : Tactic
  | stx@`(tactic| test_proof_seq $s:str $tacs:tacticSeq) => do
    let fileMap ← getFileMap
    let some stxRange := fileMap.rangeOfStx? stx | return
    let indent : Nat := 
      if let some tacsRange := fileMap.rangeOfStx? tacs.raw then
        tacsRange.start.character
      else
        stxRange.start.character + 2
    let text : String := ("\n".pushn ' ' indent) ++ s.getString
    let range : Lsp.Range := ⟨stxRange.end, stxRange.end⟩
    savePanelWidgetInfo stx ``InsertionComponent do
        return json% { text : $(text), range : $(range) }
    evalTacticSeq tacs.raw
  |             _               => throwUnsupportedSyntax