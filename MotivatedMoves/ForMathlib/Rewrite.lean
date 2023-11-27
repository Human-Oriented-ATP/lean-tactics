import Std.Lean.Position
import MotivatedMoves.ForMathlib.Basic
import MotivatedMoves.GUI.DynamicEditButton

open Lean Server Elab Meta ProofWidgets Jsx Json Parser Tactic

structure RewriteProps extends InteractiveTacticProps where
  symm : Bool
  rwRule : Name
deriving RpcEncodable

-- TODO: Move this
instance : ToString Occurrences where
  toString := fun
    | .all => ".all"
    | .pos occs => s!".pos {occs}"
    | .neg occs => s!".neg {occs}"

instance : ToString Rewrite.Config where
  toString cfg := 
    "{ " ++ s!"occs := {cfg.occs}" ++ " }"

def findRewriteOccurrence (thm : Name) (symm : Bool) (position : SubExpr.Pos) (target : Expr) : MetaM (Nat × Expr ) := do
  let env ← getEnv
  let .some ci := env.find? thm | throwError s!"Failed to find {thm} in the environment."
  let (vars, _, eqn) ← forallMetaTelescopeReducing ci.type
  let lhs : Expr :=
    match (← matchEq? eqn) with
    | some (_, lhs, rhs) => if symm then rhs else lhs
    | none =>
      match (eqn.iff?) with
      | some (lhs, rhs) => if symm then rhs else lhs
      | none => panic! s!"Received {thm}; equality or iff proof expected." 
  let occurrence ← findMatchingOccurrence position target lhs
  let pattern ← mkAppM thm <| ← vars.mapM instantiateMVars
  return (occurrence, pattern)

def rewriteTacticCall (loc : SubExpr.GoalsLocation) (goal : Widget.InteractiveGoal) (thm : Name) (symm : Bool) : MetaM String := do
  let subExpr ← loc.toSubExpr
  let (occurrence, pattern) ← findRewriteOccurrence thm symm subExpr.pos subExpr.expr
  let cfg : Rewrite.Config := { occs := .pos [occurrence] }
  let arg : String := Format.pretty <| ← ppExpr pattern
  return s!"rw (config := {cfg}) [{if symm then "← " else "" ++ arg}] {loc.loc.render goal}"

@[server_rpc_method]
def Rewrite.rpc (props : RewriteProps) : RequestM (RequestTask Html) := do
  let some loc := props.selectedLocations.back? | return .pure <p>Select a sub-expression to rewrite.</p>
  let .some goal := props.goals.find? (·.mvarId == loc.mvarId) | return .pure <p>No goals found.</p>
  let tacticStr : String ← goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      rewriteTacticCall loc goal props.rwRule props.symm
  return .pure (
        <DynamicEditButton 
          label={"Rewrite sub-term"} 
          range?={props.replaceRange} 
          insertion?={some tacticStr} 
          variant={"contained"} 
          size={"small"} />
      )

@[widget_module]
def Rewrite : Component RewriteProps :=
  mk_rpc_widget% Rewrite.rpc

syntax (name := rw_at) "rw" "[" rwRule "]" "at?" : tactic

@[tactic rw_at]
def rewriteAt : Tactic
| stx@`(tactic| rw [$rule] at?) => do
  let range := (← getFileMap).rangeOfStx? stx
  let (symm, name) :=
    match rule with
      | `(rwRule| $n:ident) => (false, n.getId)
      | `(rwRule| ← $n:ident) => (true, n.getId)
      -- | `(rwRule| <- $n:ident) => (true, n.getId)
      |       _            => panic! "Expected rewrite with identifier" 
  savePanelWidgetInfo stx ``Rewrite do
    return json% { replaceRange : $(range), symm : $(symm), rwRule : $(name) }
| _ => throwUnsupportedSyntax

example (h : 5 + 6 = 8 + 7) : 1 + 2 = (3 + 4) + (1 + 2) := by
  rw (config := { occs := .pos [1] }) [Nat.add_comm 1 2]
  sorry 