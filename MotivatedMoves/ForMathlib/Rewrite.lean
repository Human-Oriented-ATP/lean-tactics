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

@[server_rpc_method]
def Rewrite.rpc (props : RewriteProps) : RequestM (RequestTask Html) := do
  let some loc := props.selectedLocations.back? | return .pure <p>Select a sub-expression to rewrite.</p>
  let .some goal := props.goals.find? (·.mvarId == loc.mvarId) | return .pure <p>No goals found.</p>
  let tacticStr : String ← goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    let lhs : MetaM Expr := do
      let env ← getEnv
      let .some ci := env.find? props.rwRule | throwError s!"Failed to find {props.rwRule} in the environment."
      let (_, _, eqn) ← forallMetaTelescopeReducing ci.type
      match (← matchEq? eqn) with
        | some (_, lhs, rhs) => return if props.symm then rhs else lhs
        | none =>
          match (eqn.iff?) with
            | some (lhs, rhs) => return if props.symm then rhs else lhs
            | none => throwError s!"Received {props.rwRule}; equality or iff proof expected." 
    Meta.withLCtx lctx md.localInstances do
      let subExpr ← loc.toSubExpr
      let occurrence ← findOccurrence subExpr.pos subExpr.expr lhs
      let cfg : Rewrite.Config := { occs := .pos [occurrence] }
      return s!"rw (config := {cfg}) [{if props.symm then "← " else "" ++ props.rwRule.toString}] {loc.loc.render goal}" 
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

example : 1 + 2 = (1 + 2) + (1 + 2) := by
  rw (config := { occs := .pos [3] }) [Nat.add_comm]
  sorry