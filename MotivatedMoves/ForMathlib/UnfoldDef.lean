import Lean
import Std.Lean.Position
import MotivatedMoves.GUI.DynamicEditButton
import MotivatedMoves.ForMathlib.Basic

open Lean Server ProofWidgets Jsx Json Meta MonadExceptOf Elab Tactic

section
-- Jovan's `tree_rewrite_def`

partial def reduceProjection (e : Expr) : ExceptT MessageData MetaM Expr :=
  e.withAppRev fun f revArgs => match f with
    | .proj _ i b => do
      let some value ← project? b i | throw m! "could not project expression {b}"
      reduceProjection (value.betaRev revArgs)
    | _ => return e

def replaceByDefAux (e : Expr) : ExceptT MessageData MetaM Expr := do
  if let .letE _ _ v b _ := e then return b.instantiate1 v
  e.withAppRev fun f revArgs => match f with
    | .const name us => do
      let info ← getConstInfoDefn name
      let result := info.value.instantiateLevelParams info.levelParams us
      if ← isDefEq result f then
        reduceProjection (result.betaRev revArgs)
      else
        throw m! "could not replace {f} by its definition"
    | _ => do
      let result ← reduceProjection (f.betaRev revArgs)
      if result == e then throw m! "could not find a definition for {e}"
      else return result

def replaceByDef (pos : SubExpr.Pos) (e : Expr) : MetaM Expr := do
  match ← (replaceSubexpr replaceByDefAux pos e).run with
  | .error e => throwError e
  | .ok result => return result

def unfoldDefinitionAtGoalLoc (mvarId : MVarId) : SubExpr.GoalLocation → MetaM MVarId
  | .hyp _ => pure mvarId
  | .hypType fvarId pos =>
    mvarId.withContext do
      let hypType ← fvarId.getType 
      mvarId.replaceLocalDeclDefEq fvarId =<<
        replaceByDef pos hypType
  | .hypValue _ _ => pure mvarId -- TODO: Implement this case
  | .target pos => 
    mvarId.withContext do
      let target ← mvarId.getType
      mvarId.replaceTargetDefEq =<< 
        replaceByDef pos target

elab "unfold" pos:position : tactic => do
  let goalLocs ← expandPosition pos
  for goalLoc in goalLocs do
    liftMetaTactic1 (unfoldDefinitionAtGoalLoc · goalLoc)

end

section

@[server_rpc_method]
def Unfold.rpc (props : InteractiveTacticProps) : RequestM (RequestTask Html) := do
  let some loc := props.selectedLocations.back? | return .pure <p>Select a sub-expression to unfold.</p>
  let .some goal := props.goals.find? (·.mvarId == loc.mvarId) | return .pure <p>No goals found.</p>
  return .pure (
        <DynamicEditButton 
          label={"Unfold definition"} 
          range?={props.replaceRange} 
          insertion?={some s!"unfold {loc.loc.toPosition goal}"} 
          variant={"contained"} 
          size={"small"} />
      )

@[widget_module]
def Unfold : Component InteractiveTacticProps := 
  mk_rpc_widget% Unfold.rpc

elab stx:"unfold?" : tactic => do
  let range := (← getFileMap).rangeOfStx? stx 
  savePanelWidgetInfo stx ``Unfold do
    return json% { replaceRange : $(range) }

end

section Test

def f := Nat.add

example (hyp₀ hyp₁ : f 1 1 = 5) : f 1 2 = 3 := by
  unfold with position "/0/1"
  unfold  at hyp₀ with position "/0/1"
  sorry

end Test