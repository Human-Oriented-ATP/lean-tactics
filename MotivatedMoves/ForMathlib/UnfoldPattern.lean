import Lean
import Std.Lean.Position
import MotivatedMoves.GUI.DynamicEditButton
import MotivatedMoves.ForMathlib.Basic

open Lean Server Core Meta MonadExceptOf Elab Tactic
open ProofWidgets Json Jsx

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

--

def replaceByDef (e : Expr) (pattern : AbstractMVarsResult) (occs : Occurrences) : MetaM Expr := do 
  let (_, _, p) ← openAbstractMVarsResult pattern
  let eAbst ← kabstract e p occs
  unless eAbst.hasLooseBVars do
    throwError m!"Failed to find instance of pattern {indentExpr p} in {indentExpr e}."
  match ← replaceByDefAux p with
  | .ok q =>
    let e' := eAbst.instantiate1 q
    instantiateMVars e'
  | .error err => throwError err

end

open Parser Tactic Conv in
elab "unfold'" occs:(occs)? p:term loc:(location)? : tactic => do
  let pattern ← expandPattern p
  let location := (expandLocation <$> loc).getD (.targets #[] true)
  let occurrences := expandOccs occs
  let goal ← getMainGoal
  goal.withContext do 
    withLocation location
      (atLocal := fun fvarId ↦ do
        let hypType ← fvarId.getType
        let newGoal ← goal.replaceLocalDeclDefEq fvarId <| ← 
          replaceByDef hypType pattern occurrences
        replaceMainGoal [newGoal])
      (atTarget := do
        let newGoal ← goal.replaceTargetDefEq <| ←
          replaceByDef (← goal.getType) pattern occurrences  
        replaceMainGoal [newGoal])
      (failed := (throwTacticEx `unfold · m!"Failed to unfold pattern {p}."))

@[server_rpc_method]
def Unfold.rpc (props : InteractiveTacticProps) : RequestM (RequestTask Html) := do
  let some loc := props.selectedLocations.back? | return .pure <p>Select a sub-expression to unfold.</p>
  let .some goal := props.goals.find? (·.mvarId == loc.mvarId) | return .pure <p>No goals found.</p>
  let tacticStr : String ← goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let subExpr ← loc.toSubExpr
      let pattern ← SubExpr.patternAt subExpr.pos subExpr.expr
      let occurrence ← findOccurrence subExpr.pos subExpr.expr
      return s!"unfold' (occs := {occurrence}) {(← PrettyPrinter.ppExpr pattern).pretty} {loc.loc.render goal}" 
  return .pure (
        <DynamicEditButton 
          label={"Unfold definition"} 
          range?={props.replaceRange} 
          insertion?={some tacticStr} 
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

def f := Nat.add

def g (n : Nat) := n + 2

example (h : f 0 0 = g (1 + 1)) : ∀ n : Nat,  f n 1 = f 1 n := by
  unfold' (occs := 1) g (1 + 1) at h
  -- unfold' (occs := 1) (_ : Nat → Nat) (1 + 1) at h
  sorry
