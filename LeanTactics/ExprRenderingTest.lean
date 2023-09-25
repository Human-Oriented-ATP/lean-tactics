import ProofWidgets.Presentation.Expr
import ProofWidgets.Component.HtmlDisplay

open Lean Server Widget ProofWidgets Jsx

def Lean.Widget.CodeWithInfos.addDiffs (diffs : AssocList SubExpr.Pos DiffTag) (code : CodeWithInfos) : CodeWithInfos := 
  code.map fun info ↦
    match diffs.find? info.subexprPos with
      | some diff => { info with diffStatus? := some diff }
      |    none   =>   info

def Lean.Expr.renderWithDiffs (e : Expr) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do 
  let e' := (← Widget.ppExprTagged e).addDiffs diffs
  return <InteractiveCode fmt={e'} />

def Lean.Name.renderWithDiffs (nm : Name) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do
  let env ← getEnv
  let some ci := env.find? nm | failure
  ci.type.renderWithDiffs diffs


def myDiffs : AssocList SubExpr.Pos DiffTag := 
  AssocList.empty 
  |>.insert (.ofArray #[1, 1, 0, 1]) .wasChanged 
  |>.insert (.ofArray #[1, 1, 1]) .willChange

syntax (name := exprCmd) "#expr " term : command

open Elab Command Json in
@[command_elab exprCmd]
def elabHtmlCmd : CommandElab := fun
  | stx@`(#expr $t:term) =>
    runTermElabM fun _ => do
      let trm ← Term.elabTerm t none
      let e ← ExprWithCtx.save trm
      let ht := <ExprPresentation expr={{ val := e }} />
      savePanelWidgetInfo stx ``HtmlDisplay do
        return json% { html: $(← rpcEncode ht) }
  | stx => throwError "Unexpected syntax {stx}."

@[expr_presenter]
def myExprPresenter : ExprPresenter := {
  userName := "MyPresenter",
  layoutKind := .inline,
  present := fun _ ↦ pure <b> Test </b>
}

#expr (1 + 1 = 2)