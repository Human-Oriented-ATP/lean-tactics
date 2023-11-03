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

def mkLocation (hyps : Array String) : TSyntax ``location :=
  let locs : TSyntaxArray `term := hyps.map (Coe.coe ∘ Syntax.mkStrLit)
  ⟨
    .node .none `Lean.Parser.Tactic.location
      #[Lean.Syntax.atom (Lean.SourceInfo.none) "at",
        .node .none `Lean.Parser.Tactic.locationHyp
          #[.node .none `null locs,
            .node .none `null #[]]]
  ⟩

def Lean.SubExpr.GoalLocation.toPosition (goal : Widget.InteractiveGoal) : SubExpr.GoalLocation → TSyntax ``position
  | .hyp fvarId =>
      let loc := mkLocation (fvarId.getUserNames goal)
      -- `(position| $loc with position "/")
      ⟨
      .node .none `position
        #[.node .none `null #[loc],
        .atom .none "with position",
        .node .none `str #[.atom .none "\"/\""]]
      ⟩
  | .hypType fvarId pos =>
      let loc := mkLocation (fvarId.getUserNames goal)
      -- `(position| $loc with position $(pos.toStrLit))
      ⟨
      .node .none `position
        #[.node .none `null #[loc],
        .atom .none "with position",
        .node .none `str #[.atom .none pos.toString]]
      ⟩
  | .hypValue fvarId pos =>
      -- TODO: Treat this case properly
      -- `(position| at * with position "/") 
      ⟨
      .node .none `position
        #[.node .none `null
            #[.node .none `Lean.Parser.Tactic.location
                #[.atom .none "at",
                  .node .none `Lean.Parser.Tactic.locationWildcard
                    #[.atom .none "*"]]],
          .atom .none "with position",
          .node .none `str #[.atom .none "\"/\""]]
      ⟩
  | .target pos => 
      -- `(position| with position $(pos.toStrLit))
      ⟨
      .node .none `position
        #[.node .none `null
            #[.node .none `Lean.Parser.Tactic.location #[]],
          .atom .none "with position",
          .node .none `str #[.atom .none pos.toString]]
      ⟩

end

structure InteractiveTacticProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
deriving RpcEncodable

-- def mkInteractiveTactic 
--     (method : Array SubExpr.GoalsLocation → ExceptT String MetaM Html) 
--     (props : InteractiveTacticProps) : RequestM (RequestTask Html) :=
--   RequestM.asTask do
--     _