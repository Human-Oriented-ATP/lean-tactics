import ProofWidgets.Presentation.Expr
import ProofWidgets.Component.HtmlDisplay

open Lean Server Widget ProofWidgets Jsx

def Lean.Widget.CodeWithInfos.addDiffs (diffs : AssocList SubExpr.Pos DiffTag) (code : CodeWithInfos) : CodeWithInfos := 
  code.map fun info ↦
    match diffs.find? info.subexprPos with
      | some diff => { info with diffStatus? := some diff }
      |    none   =>   info

def Lean.Name.renderWithDiffs (nm : Name) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do
  let env ← getEnv
  let some ci := env.find? nm | failure
  let type := ci.type
  let ttype := (← Widget.ppExprTagged type).addDiffs diffs
  return <InteractiveCode fmt={ttype} />

def myDiffs : AssocList SubExpr.Pos DiffTag := 
  AssocList.empty 
  |>.insert (.ofArray #[1, 1, 0, 1]) .wasChanged 
  |>.insert (.ofArray #[1, 1, 1]) .willChange

syntax (name := exprCmd) "#expr " name : command

open Elab Command Json in
@[command_elab exprCmd]
def elabHtmlCmd : CommandElab := fun
  | stx@`(#expr $n:name) =>
    runTermElabM fun _ => do
      let ht ← n.getName.renderWithDiffs myDiffs
      savePanelWidgetInfo stx ``HtmlDisplay do
        return json% { html: $(← rpcEncode ht) }
  | stx => throwError "Unexpected syntax {stx}."

#expr `Nat.add_comm