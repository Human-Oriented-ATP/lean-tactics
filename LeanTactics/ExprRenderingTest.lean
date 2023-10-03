import ProofWidgets
import Paperproof
import Mathlib.Tactic
import Std

open Lean Server Widget ProofWidgets Jsx

syntax (name := showExpr) "#show_expr" term : command

open Elab Command Json in
@[command_elab showExpr]
def showExprImpl : CommandElab := fun
  | stx@`(command| #show_expr $t) => do
    runTermElabM fun _ => do
      let trm ← Term.elabTerm t none
      let e ← Widget.ppExprTagged trm -- replace with custom function 
      let code : Html := <InteractiveCode fmt={e} />
      savePanelWidgetInfo stx ``HtmlDisplay do
        return json% { html: $(← rpcEncode code) }
  | stx => throwError "Unexpected syntax {stx}."

#show_expr 1 = 1


#exit

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

syntax (name := exprTemp) "!expr " term : command

structure ExprPresentProps extends PanelWidgetProps where
  expr : CodeWithInfos
deriving RpcEncodable

@[widget_module] def InteractiveExprPresent : Component ExprPresentProps where
  javascript := include_str ".." / "build" / "js" / "interactiveExpr.js"

open Elab Command Json in
@[command_elab exprTemp]
def elabExpr : CommandElab := fun
  | stx@`(!expr $t:term) =>
    runTermElabM fun _ => do
      let trm ← Term.elabTerm t none
      let e ← ExprWithCtx.save trm
      let some pos := (← getFileMap).rangeOfStx? stx | failure
      let tgt ← ppExprTagged e.expr 
      let ht := <InteractiveExprPresent pos = {pos.end} goals = {#[]} termGoal? = {none} selectedLocations = {#[]} expr = {tgt} />
      savePanelWidgetInfo stx ``HtmlDisplay do
        return json% { html: $(← rpcEncode ht) }
  | stx => throwError "Unexpected syntax {stx}."

theorem Temp (h : 1 = 2): ∀ n : Nat, 1 = 1 ∨ 1 = 1 := by 
  intro n
  left
  sorry

example (α : Type) (s t : Set α) : s ∩ t = t ∩ s := by
  ext x
  constructor
  intro h
  rw [Set.mem_inter_iff] at h ⊢
  constructor
  exact h.2
  -- exact h.1
  sorry

-- Expressions can now be `shift-clicked`!!!
!expr ((1 : Nat) + 1 = 2)