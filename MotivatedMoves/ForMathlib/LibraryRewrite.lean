import Mathlib.Tactic.Rewrites
import MotivatedMoves.ForMathlib.Rewrite
import MotivatedMoves.GUI.DynamicEditButton
import MotivatedMoves.LibrarySearch.LibrarySearch

open Lean Meta Server ProofWidgets Jsx

structure RewriteLemma where
  name : Name
  symm : Bool
  deletedPos : SubExpr.Pos
  insertedPos : SubExpr.Pos
deriving BEq, Inhabited

def RewriteLemma.length (rwLemma : RewriteLemma) : Nat :=
  rwLemma.name.toString.length

def RewriteLemma.diffs (rwLemma : RewriteLemma) : Lean.AssocList SubExpr.Pos Widget.DiffTag :=
  .cons rwLemma.insertedPos .wasInserted
  (.cons rwLemma.deletedPos .wasDeleted .nil)

def updateRewriteTree (name : Name) (cinfo : ConstantInfo) (discrTree : RefinedDiscrTree RewriteLemma) : MetaM (RefinedDiscrTree RewriteLemma) := do
  if Tree.isBadDecl name cinfo (← getEnv) then
    return discrTree

  let stmt := cinfo.type
  let (vars, _, eqn) ← forallMetaTelescopeReducing stmt
  let .some (lhs, rhs) ← matchEqn? eqn | return discrTree
  let eqnPos : SubExpr.Pos := vars.foldl (init := .root) (fun pos _ => pos.pushAppArg)
  let lhsPos := eqnPos.pushAppFn.pushAppArg
  let rhsPos := eqnPos.pushAppArg
  let discrTree ← discrTree.insert (e := lhs) (v := { name, symm := false, deletedPos := lhsPos, insertedPos := rhsPos })
  discrTree.insert (e := rhs) (v := { name, symm := true, deletedPos := rhsPos, insertedPos := lhsPos })

section

open Std Tactic

@[reducible]
def RewriteCache := DeclCache (RefinedDiscrTree RewriteLemma × RefinedDiscrTree RewriteLemma)

def RewriteCache.mk (profilingName : String)
  (init : Option (RefinedDiscrTree RewriteLemma) := none) :
    IO RewriteCache :=
  DeclCache.mk profilingName (pre := pre) ({}, {})
    addDecl addLibraryDecl (post := post)
where
  pre := do
    let .some libraryTree := init | failure
    return ({}, libraryTree)
  addDecl (name : Name) (cinfo : ConstantInfo)
    | (currentTree, libraryTree) => do
    return (← updateRewriteTree name cinfo currentTree, libraryTree)
  addLibraryDecl (name : Name) (cinfo : ConstantInfo)
    | (currentTree, libraryTree) => do
    return (currentTree, ← updateRewriteTree name cinfo libraryTree)
  sortRewriteLemmas : Array RewriteLemma → Array RewriteLemma :=
    Array.qsort (lt := (·.length < ·.length))
  post
    | (currentTree, libraryTree) => do
    return (currentTree, libraryTree.mapArrays sortRewriteLemmas)

def cachePath : IO System.FilePath := do
  try
    return (← findOLean `LibraryRewrite.RewriteLemmas).withExtension "extra"
  catch _ =>
    return "build" / "lib" / "LibraryRewrite" / "RewriteLemmas.extra"

initialize cachedData : RewriteCache ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle (RefinedDiscrTree RewriteLemma) path
    -- We can drop the `CompactedRegion` value; we do not plan to free it
    RewriteCache.mk "rewrite lemmas : using cache" (init := some d)
  else
    RewriteCache.mk "rewrite lemmas : init cache"

def getRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma × RefinedDiscrTree RewriteLemma) :=
  cachedData.get

end

section

open Widget

def mkDiv (elems : Array Html) (cfg : Array (String × Json) := #[]) : Html :=
  .element "div" cfg elems

def Lean.Widget.CodeWithInfos.addDiffs (diffs : AssocList SubExpr.Pos DiffTag) (code : CodeWithInfos) : CodeWithInfos :=
  code.map fun info =>
    match diffs.find? info.subexprPos with
      | some diff => { info with diffStatus? := some diff }
      |    none   =>   info

def Lean.Expr.renderWithDiffs (e : Expr) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do
  let e' := (← Widget.ppExprTagged e).addDiffs diffs
  return <InteractiveCode fmt={e'} />

def Lean.Name.renderWithDiffs (nm : Name) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do
  let env ← getEnv
  let some ci := env.find? nm | failure
  ci.type.renderWithDiffs diffs

def renderResult
  (loc : SubExpr.GoalsLocation)
  (goal : Widget.InteractiveGoal)
  (range : Lsp.Range)
  (rwLemma : RewriteLemma) : MetaM (Option Html) := do
  let some tacticCall ← (try? do
    rwCall loc goal (← abstractMVars <| ← mkConstWithLevelParams rwLemma.name) rwLemma.symm)
    | return none
  return mkDiv
    #[← rwLemma.name.renderWithDiffs rwLemma.diffs,
        <DynamicEditButton
          label={rwLemma.name.toString}
          range?={range}
          insertion?={tacticCall}
          variant={"text"}
          color={"info"}
          onWhitespace={false}
          size={"small"} />]
    #[("display", "flex"), ("justifyContent", "space-between")]

end

def getMatches (subExpr : SubExpr) : MetaM (Array RewriteLemma) := do
  let (localLemmas, libraryLemmas) ← getRewriteLemmas
  viewSubexpr (p := subExpr.pos) (root := subExpr.expr) fun _fvars s => do
    let localResults ← localLemmas.getMatchWithScore s (unify := true) (config := {})
    let libraryResults ← libraryLemmas.getMatchWithScore s (unify := true) (config := {})
    let allResults := localResults ++ libraryResults -- TODO: filtering
    return allResults.concatMap Prod.fst



@[server_rpc_method]
def LibraryRewrite.rpc (props : InteractiveTacticProps) : RequestM (RequestTask Html) := do
  let some loc := props.selectedLocations.back? | return .pure <p>Select an expression to rewrite.</p>
  let some goal := props.goals.find? (·.mvarId == loc.mvarId) | return .pure <p>No goals found.</p>
  let some (core : Html) ← (goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let target ← loc.toSubExpr
      let results ← getMatches target
      let suggestions ← results.foldlM (init := #[]) fun suggestions result => do
        match ← renderResult loc goal props.replaceRange result with
        | some suggestion => return suggestions.push suggestion
        | none => return suggestions
      if suggestions.isEmpty then
        return none
      return mkDiv suggestions) | return .pure <p>No library rewrites found.</p>
  return .pure (
    <details «open»={true}>
      <summary className="mv2 pointer">{.text "Library rewrites:"}</summary>
      {core}
    </details>)

@[widget_module]
def LibraryRewrite : Component InteractiveTacticProps :=
  mk_rpc_widget% LibraryRewrite.rpc

elab stx:"lib_rw?" : tactic => do
  let range := (← getFileMap).rangeOfStx? stx
  Widget.savePanelWidgetInfo (hash LibraryRewrite.javascript) (stx := stx) do
    return json% { replaceRange : $(range) }
