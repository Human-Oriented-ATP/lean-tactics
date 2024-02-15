import Std.Lean.Position
import MotivatedMoves.ForMathlib.Utils
import MotivatedMoves.GUI.DynamicEditButton

/-!

# Point-and-click rewriting

This file defines a widget for making targeted rewrites by
pointing and clicking sub-expressions in the infoview.

Once a sub-expression is selected, a `rw` tactic call with
a configuration targeting the selected location is generated.

-/

open Lean Server Elab Meta ProofWidgets Jsx Json Parser Tactic

/-- `Props` for point-and-click rewriting. -/
structure RewriteProps extends InteractiveTacticProps where
  /-- A flag to indicate whether to rewrite in reverse. -/
  symm : Bool
  /-- An expression representing the argument of the rewrite tactic. -/
  rwRule : WithRpcRef AbstractMVarsResult

deriving instance TypeName for AbstractMVarsResult
#mkrpcenc RewriteProps

section

/-- Convert `Occurrences` to a `String`. -/
instance : ToString Occurrences where
  toString := fun
    | .all => ".all"
    | .pos occs => s!".pos {occs}"
    | .neg occs => s!".neg {occs}"

-- /-- Convert a `Rewrite.Config` to a `String`.
--     This instance is restricted to printing just the information about the occurrences. -/
-- instance : ToString Rewrite.Config where
--   toString cfg :=
--     s! "\{ occs := {cfg.occs} }"

/-- Extract the left and right hand sides of an equality or iff statement. -/
def matchEqn? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← matchEq? e with
  | some (_, lhs, rhs) => return (lhs, rhs)
  | none => return e.iff?

end

/-- Specialises the theorem to match the sub-expression at the given position
    and calculates its occurrence number in the whole expression. -/
def findRewriteOccurrence (thm : Expr) (symm : Bool)
    (position : SubExpr.Pos) (target : Expr) : MetaM (Occurrences × Expr) := do
  let stmt ← inferType thm
  let (vars, _, eqn) ← forallMetaTelescopeReducing stmt
  let .some (lhs, rhs) ← matchEqn? eqn |
    panic! s!"Received {stmt}; equality or iff proof expected."
  let hs := if symm then rhs else lhs
  let occurrence ← findMatchingOccurrence position target hs
  let pattern := mkAppN thm <| ← vars.mapM instantiateMVars
  return (occurrence, pattern)

/-- Generates a rewrite tactic call with configuration from the arguments. -/
def rwCall (loc : SubExpr.GoalsLocation) (goal : Widget.InteractiveGoal)
    (thmAbst : AbstractMVarsResult) (symm : Bool) : MetaM String := do
  let subExpr ← loc.toSubExpr
  let us ← thmAbst.paramNames.mapM <| fun _ ↦ mkFreshLevelMVar
  let thm := thmAbst.expr.instantiateLevelParamsArray thmAbst.paramNames us
  let (occurrence, pattern) ← findRewriteOccurrence thm symm subExpr.pos subExpr.expr
  let cfg := if occurrence matches .all then ""
    else
      s! " (config := \{ occs := {occurrence} })"
  let arg := Format.pretty <| ← ppExpr pattern
  return s! "rw{cfg} [{if symm then "← " else ""}{arg}]{loc.loc.render goal}"

@[server_rpc_method]
def Rewrite.rpc (props : RewriteProps) : RequestM (RequestTask Html) := do
  let some loc := props.selectedLocations.back? | return .pure <p>Select a sub-expression to rewrite.</p>
  let .some goal := props.goals.find? (·.mvarId == loc.mvarId) | return .pure <p>No goals found.</p>
  let tacticStr : String ← goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      rwCall loc goal props.rwRule.val props.symm
  return .pure (
        <DynamicEditButton
          label={"Rewrite sub-term"}
          range?={props.replaceRange}
          insertion?={some tacticStr}
          variant={"contained"}
          onWhitespace={false}
          size={"small"} />
      )

@[widget_module]
def Rewrite : Component RewriteProps :=
  mk_rpc_widget% Rewrite.rpc

syntax (name := rw_at) "rw" "[" rwRule "]" "at?" : tactic

@[tactic rw_at]
def rewriteAt : Tactic
| stx@`(tactic| rw [$rule] at?) => do
  let .some range := (← getFileMap).rangeOfStx? stx | throwError s!"Could not find range of syntax {stx}."
  let (symm, arg) :=
    match rule with
      | `(rwRule| $arg:term) => (false, arg)
      | `(rwRule| ← $arg:term) => (true, arg)
      -- | `(rwRule| <- $arg:term) => (true, arg)
      |       _            => panic! s!"Failed to process {rule}."
  let argAbst ← abstractMVars <| ← elabTerm arg none
  Widget.savePanelWidgetInfo (hash Rewrite.javascript) (stx := stx) do
    return json% {
      replaceRange : $(range),
      symm : $(symm),
      rwRule : $(← rpcEncode (WithRpcRef.mk argAbst))
      }
| _ => throwUnsupportedSyntax


section Demo

example (h : 5 + 6 = 8 + 7) : 1 + 2 = (3 + 4) + (1 + 2) := by
  rw (config := { occs := .all }) [Nat.add_comm 1 2]
  rw [Nat.add_comm] at? -- select the sub-expression `5 + 6`
  sorry

end Demo
