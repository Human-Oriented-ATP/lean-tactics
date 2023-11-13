import Lean
import ProofWidgets

open Lean Server ProofWidgets Elab Tactic Parser Tactic
section

def Lean.FVarId.getUserNames (fvarId : FVarId) (goal : Widget.InteractiveGoal) : Array String :=
  let hyps := goal.hyps.filter (·.fvarIds.contains fvarId)
  hyps.concatMap (·.names)

def Lean.SubExpr.GoalsLocation.toSubExpr : SubExpr.GoalsLocation → MetaM SubExpr 
  | ⟨mvarId, .hyp fvarId⟩ => mvarId.withContext do
      return ⟨← fvarId.getType, .fromString! "/"⟩
  | ⟨mvarId, .hypType fvarId pos⟩ => mvarId.withContext do 
      return ⟨← fvarId.getType, pos⟩
  | ⟨mvarId, .hypValue fvarId pos⟩ => mvarId.withContext do
      let .some val ← fvarId.getValue? | unreachable!
      return ⟨val, pos⟩
  | ⟨mvarId, .target pos⟩ => do return ⟨← mvarId.getType, pos⟩

def Lean.SubExpr.GoalLocation.render (goal : Widget.InteractiveGoal) : SubExpr.GoalLocation → String
  | .hyp fvarId => renderLocation (fvarId.getUserNames goal) false
  | .hypType fvarId _ => renderLocation (fvarId.getUserNames goal) false
  | .hypValue fvarId _ => "" -- TODO: Handle this case
  | .target _ => ""
where 
  renderLocation (hyps : Array String) (type : Bool) : String :=
    "at " ++ " ".intercalate hyps.toList ++ (if type then " ⊢" else "")

end

structure InteractiveTacticProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
deriving RpcEncodable