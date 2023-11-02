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

def Lean.SubExpr.Pos.toStrLit (pos : SubExpr.Pos) : StrLit :=
  Syntax.mkStrLit pos.toString

def Lean.FVarId.getUserNames (fvarId : FVarId) (goal : Widget.InteractiveGoal) : Array String :=
  let hyps := goal.hyps.filter (·.fvarIds.contains fvarId)
  hyps.concatMap <| fun hyp ↦ 
    (Array.zip hyp.names hyp.fvarIds).filterMap <| fun (name, id) ↦
      if id == fvarId then some name else none

def mkLocation (hyps : Array String) [Monad M] [MonadQuotation M] : M (TSyntax ``location) :=
  let locs : TSyntaxArray `term := hyps.map (Coe.coe ∘ Syntax.mkStrLit)
  `(location| at $[$locs]*)

def Lean.SubExpr.GoalLocation.toPosition [Monad M] [MonadQuotation M] (goal : Widget.InteractiveGoal) : SubExpr.GoalLocation → M (TSyntax ``position)
  | .hyp fvarId => do
      let loc ← mkLocation (fvarId.getUserNames goal)
      `(position| $loc with position "/")
  | .hypType fvarId pos => do
      let loc ← mkLocation (fvarId.getUserNames goal)
      `(position| $loc with position $(pos.toStrLit))
  | .hypValue fvarId pos => `(position| at * with position "/") -- TODO: Treat this case properly
  | .target pos => `(position| with position $(pos.toStrLit))

end

structure InteractiveTacticProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
deriving RpcEncodable

-- def mkInteractiveTactic 
--     (method : Array SubExpr.GoalsLocation → ExceptT String MetaM Html) 
--     (props : InteractiveTacticProps) : RequestM (RequestTask Html) :=
--   RequestM.asTask do
--     _