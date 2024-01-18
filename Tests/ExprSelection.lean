import ProofWidgets.Component.HtmlDisplay

open Lean Widget Server ProofWidgets Jsx Json

structure ExprSelectionProps where
  expr : CodeWithInfos
  subexprPos : String
deriving RpcEncodable

structure ExprDisplayProps extends ExprSelectionProps where
  description : String
deriving RpcEncodable

structure ExprsDisplayProps where
  exprs : Array ExprDisplayProps
deriving RpcEncodable

@[widget_module]
def ExprsDisplay : Component ExprsDisplayProps where
  javascript := include_str "../build/js/exprDisplay.js"

syntax (name := exprCmd) "#expr " term : command

open Elab Command Json in
@[command_elab exprCmd]
def elabHtmlCmd : CommandElab := fun
  | stx@`(#expr $t:term) =>
    runTermElabM fun _ => do
      let trm ← Term.elabTerm t none
      let e ← Widget.ppExprTagged trm
      let ht := <ExprsDisplay exprs={#[{expr := e, subexprPos := "", description := "Test"}]} />
      Widget.savePanelWidgetInfo (hash HtmlDisplay.javascript) (stx := stx) do
        return json% { html: $(← rpcEncode ht) }
  | stx => throwError "Unexpected syntax {stx}."

#expr 1 + 1