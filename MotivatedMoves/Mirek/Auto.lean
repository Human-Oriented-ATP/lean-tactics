import Lean

open Lean Elab Meta

def Expr.render (e : Expr) : MetaM String := do
  return toString (← ppExpr e)

elab "auto" : tactic => do
  let forbidden := #[`grasshopper_ih]
  let localDecls := (← getLCtx).decls.toArray.filterMap id |>.filter fun decl ↦ !(decl.kind == .implDetail || forbidden.contains decl.userName.getRoot)
  let context : Array String ← localDecls.filterMapM fun decl ↦ do
    if ← isProp decl.type then
      logInfo m!"Proposition in context: {decl.userName}"
      return none
    else
      return s!"{decl.userName.getRoot.toString} : {← Expr.render decl.type}"
  logInfo m!"Local context: {context}"
  let hypotheses : Array String ← localDecls.filterMapM fun decl ↦ do
    if ← isProp decl.type then
      Expr.exportTheorem decl.type
    else return none
  logInfo m!"Hypotheses: {hypotheses}"
  let mainGoal ← Expr.exportTheorem (← getMainTarget)
  let output : String := (context ++ #["\n---"] ++ hypotheses ++ #["\n---"] ++ #[mainGoal])
    |>.map (String.push · '\n') |>.foldl (init := "") String.append
  -- logInfo output
  if let some fileName := fileName? then
    IO.FS.writeFile fileName.getString output
  evalTactic <| ← `(tactic| sorry)
