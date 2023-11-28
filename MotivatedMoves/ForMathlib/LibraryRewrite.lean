import Mathlib.Tactic.Rewrites
import Std.Lean.Position
import MotivatedMoves.ForMathlib.Rewrite
import MotivatedMoves.GUI.DynamicEditButton
import MotivatedMoves.LibrarySearch.LibrarySearch

open Lean Std Server Elab Meta ProofWidgets Jsx Json Parser Tactic

structure RewriteLemma where
  name : Name
  symm : Bool
  deletedPos : SubExpr.Pos
  insertedPos : SubExpr.Pos
deriving BEq

def processLemma (decl : Name) (cinfo : ConstantInfo) (discrTree : Std.DiscrTree RewriteLemma) : MetaM (Std.DiscrTree RewriteLemma) := do
  let stmt := cinfo.type
  let (vars, _, eqn) ← forallMetaTelescopeReducing stmt
  let .some (lhs, rhs) ← matchEqn? eqn | return discrTree
  let eqnPos : SubExpr.Pos := vars.foldl (init := .root) (fun pos _ ↦ pos.pushAppArg)
  let lhsPos := eqnPos.pushAppFn.pushAppArg
  let rhsPos := eqnPos.pushAppArg
  (pure discrTree) 
    >>= DiscrTree.insert (e := lhs) (v := { name := decl, symm := false, deletedPos := lhsPos, insertedPos := rhsPos }) 
    >>= DiscrTree.insert (e := rhs) (v := { name := decl, symm := true, deletedPos := rhsPos, insertedPos := lhsPos })

-- @[server_rpc_method]
-- def LibraryRewrite.rpc (props : InteractiveTacticProps) : RequestM (RequestTask Html) := do
--   let some loc := props.selectedLocations.back? | return .pure <p>Select a sub-expression to rewrite.</p>
--   let .some goal := props.goals.find? (·.mvarId == loc.mvarId) | return .pure <p>No goals found.</p>
--   let tacticStr : String ← goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
--     let md ← goal.mvarId.getDecl
--     let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
--     Meta.withLCtx lctx md.localInstances do
--       let subExpr ← loc.toSubExpr
--       let lems ← Mathlib.Tactic.Rewrites.rewriteLemmas.get
--       let results ← viewSubexpr (p := subExpr.pos) (root := subExpr.expr) <| fun vars e ↦ do
--         return (← lems.1.getUnify e) ++ (← lems.2.getUnify e)
--       _  
--   return .pure (
--         <DynamicEditButton 
--           label={"Rewrite sub-term"} 
--           range?={props.replaceRange} 
--           insertion?={some tacticStr} 
--           variant={"contained"} 
--           size={"small"} />
--       )

-- @[widget_module]
-- def LibraryRewrite : Component InteractiveTacticProps :=
--   mk_rpc_widget% LibraryRewrite.rpc

-- elab stx:"lib_rw?" : tactic => do
--   let range := (← getFileMap).rangeOfStx? stx
--   savePanelWidgetInfo stx ``LibraryRewrite do
--     return json% { replaceRange : $(range) }

