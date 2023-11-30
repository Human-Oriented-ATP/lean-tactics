import Std.Lean.Position
import MotivatedMoves.ForMathlib.Utils
import MotivatedMoves.GUI.DynamicEditButton

open Lean Server Elab Meta ProofWidgets Jsx Json Parser Tactic

/-- `Props` for the point-and-click rewrite tactic. -/
structure RewriteProps extends InteractiveTacticProps where
  /-- A flag to indicate whether to rewrite in reverse. -/
  symm : Bool
  /-- The name of the lemma to rewrite with. -/
  rwRule : Name -- TODO: Make this a term
deriving RpcEncodable

section

/-- Convert `Occurrences` to a `String`. -/
instance : ToString Occurrences where
  toString := fun
    | .all => ".all"
    | .pos occs => s!".pos {occs}"
    | .neg occs => s!".neg {occs}"

/-- Convert a `Rewrite.Config` to a `String`.
    This instance is restricted to printing just the information about the occurrences. -/
instance : ToString Rewrite.Config where
  toString cfg := 
    "{ " ++ s!"occs := {cfg.occs}" ++ " }"

/-- Extract the left and right hand sides of an equality or iff statement. -/
def matchEqn? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← matchEq? e with
  | some (_, lhs, rhs) => return (lhs, rhs)
  | none => return e.iff?

end  

def findRewriteOccurrence (thm : Expr) (symm : Bool) 
    (position : SubExpr.Pos) (target : Expr) : MetaM (Nat × Expr) := do
  let stmt ← inferType thm
  let (vars, _, eqn) ← forallMetaTelescopeReducing stmt
  let .some (lhs, rhs) ← matchEqn? eqn | 
    panic! s!"Received {stmt}; equality or iff proof expected."
  let hs := if symm then rhs else lhs
  let occurrence ← findMatchingOccurrence position target hs
  let pattern := mkAppN thm <| ← vars.mapM instantiateMVars
  return (occurrence, pattern)

def rewriteTacticCall (loc : SubExpr.GoalsLocation) (goal : Widget.InteractiveGoal) 
    (thm : Name) (symm : Bool) : MetaM String := do
  let subExpr ← loc.toSubExpr
  let (occurrence, pattern) ← findRewriteOccurrence (← mkConstWithLevelParams thm) symm subExpr.pos subExpr.expr
  let cfg : Rewrite.Config := { occs := .pos [occurrence] }
  let arg : String := Format.pretty <| ← ppExpr pattern
  return s!"rw (config := {cfg}) [{if symm then "← " else "" ++ arg}]{loc.loc.render goal}"

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


section Demo

example (h : 5 + 6 = 8 + 7) : 1 + 2 = (3 + 4) + (1 + 2) := by
  rw (config := { occs := .all }) [Nat.add_comm 1 2]
  rw [Nat.add_comm] at?
  sorry

end Demo