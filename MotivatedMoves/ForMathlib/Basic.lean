import Lean
import ProofWidgets

open Lean Server ProofWidgets Elab Tactic Parser Tactic
section

syntax position := (location)? " with position " str

def expandPosition : TSyntax ``position → TacticM (Array SubExpr.GoalLocation)
| `(position| $[$loc?:location]? with position $p:str) =>
  let pos : SubExpr.Pos := .fromString! p.getString
  match expandLocation <$> loc? with
    | none => return #[.target pos]
    | some (.targets hyps type) => withMainContext do
      let fvarIds ← hyps.mapM getFVarId 
      expandPositionAux fvarIds type pos
    | some .wildcard => withMainContext do
      expandPositionAux (← getMainDecl).lctx.getFVarIds true pos
|  _ => return #[]
where
  expandPositionAux (hyps : Array FVarId) (type : Bool) (pos : SubExpr.Pos) : TacticM (Array SubExpr.GoalLocation) := do
    let hypLocs := hyps.map (.hypType · pos)
    if type then
      return hypLocs.push (.target pos)
    else
      return hypLocs

def Lean.FVarId.getUserNames (fvarId : FVarId) (goal : Widget.InteractiveGoal) : Array String :=
  let hyps := goal.hyps.filter (·.fvarIds.contains fvarId)
  hyps.concatMap <| fun hyp ↦ 
    (Array.zip hyp.names hyp.fvarIds).filterMap <| fun (name, id) ↦
      if id == fvarId then some name else none

def Lean.SubExpr.GoalLocation.toPosition (goal : Widget.InteractiveGoal) : SubExpr.GoalLocation → String
  | .hyp fvarId =>
      s!"{renderLocation (fvarId.getUserNames goal) false} with position {renderPos .root}"
  | .hypType fvarId pos =>
      s!"{renderLocation (fvarId.getUserNames goal) false} with position {renderPos pos}"
  | .hypValue fvarId pos => "" -- TODO: Handle this case
  | .target pos => s!"with position {renderPos pos}"
where 
  renderLocation (hyps : Array String) (type : Bool) : String :=
    " at " ++ " ".intercalate hyps.toList ++ (if type then " ⊢" else "")
  renderPos (pos : SubExpr.Pos) : String :=
    s!"\"{pos.toString}\""

end

structure InteractiveTacticProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
deriving RpcEncodable