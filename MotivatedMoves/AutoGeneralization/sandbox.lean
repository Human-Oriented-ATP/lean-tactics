import Lean
import Qq

open Lean Qq Elab Tactic Meta Term Command

def printMVarsInContext : MetaM Unit := do
  let m ← getMCtx
  logInfo m!"MVar Context: {(m.decls.toList.map (fun d =>
    m!"Name: {d.fst.name} Kind:{repr d.snd.kind} "
    --m!"{d.fst}"
  ))}"

def printMVarsAssignmentsInContext : MetaM Unit := do
  let m ← getMCtx
  logInfo m!"MVar Context:
    {(m.eAssignment.toList.map (fun d =>
    m!"Mvar:
      {d.fst.name}
    Assignment:
      {repr d.snd}"

  ))}"

/- Replaces all subexpressions where "condition" holds with the "replacement" in the expression e -/
def replaceWhere (condition : Expr → Bool) (replacement : Expr) (e : Expr)   : MetaM Expr := do
  if condition e then
    return replacement
  match e with
    | .app f a => return .app (← replaceWhere condition replacement f) (← replaceWhere condition replacement a)
    | .lam n a b bi => return .lam n a (← replaceWhere condition replacement b) bi
    | .forallE n a b bi => return .forallE n a (← replaceWhere condition replacement b) bi
    | _ =>  return e

def getMVarAssignedToMData : MetaM MVarId := do
  let mctx ← getMCtx
  for (mvarId, expr) in mctx.eAssignment do
    if Expr.isMData expr then
      return mvarId
  throwError "No metavariable assigned to an expression with metadata found"

/- Instantiates all mvars in e except the mvar given by m -/
def instantiateMVarsExcept (mv : MVarId) (e : Expr)  : MetaM Expr := do
  -- remove the assignment
  let mctx ← getMCtx
  let mctxassgn := mctx.eAssignment.erase mv
  setMCtx {mctx with eAssignment := mctxassgn} -- mctxassgn
  -- instantiate mvars
  let e ← instantiateMVars e
  return e

elab "test'" : tactic => do
  let userSelected ← mkFreshExprMVarQ q(Nat)
  let userMVarId := userSelected.mvarId!
  let userSelectedAnnotated := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ .mvar userMVarId
  let e := mkApp2 q(@HAdd.hAdd Nat Nat Nat instHAdd) userSelectedAnnotated q(3 + 3)
  let x ← mkFreshExprMVarQ q(Nat)
  let y ← mkFreshExprMVarQ q(Nat)
  let e' := q($y + ($y + $x))
  let e' := Expr.mdata .empty e'
  logInfo m!"mvar e {e}"
  logInfo m!"mvar e' {e'}"
  logInfo m!"def eq {← isDefEq e' e }" -- the one that comes second is the one that gets its mvar borrowed in assignments
  -- let e' ← instantiateMVarsExcept userMVarId e'
  logInfo m!"instantiated e {e}"
  logInfo m!"instantiated e' {e'}"
  -- printMVarsAssignmentsInContext
  let m ← getMVarAssignedToMData
  logInfo m!"the assigned one is {m.name}"
  -- absract anything with metadata
  let e' ← instantiateMVarsExcept m e'

  -- let e' ← replaceWhere (Expr.isMData) (← mkFreshExprMVar none) e'
  logInfo m!"replaced e' {e'}"
  -- logInfo m!"full e' {repr e'}"
  return

example : True := by
  test'
  simp

elab "test" : tactic => do
  let x ← mkFreshExprMVarQ q(Nat) -- read only
  let e := q(3 + $x)              -- read only
  withNewMCtxDepth do
    let y ← mkFreshExprMVarQ q(Nat)
    let e' := q($y + 4)
    logInfo m!"def eq {← isDefEq e e'}"
    check e'

    let e' ← instantiateMVars e'
    check e'
    logInfo m!"instantiated e' {e'}"
    return

example : True := by
  test
  simp

#eval show MetaM Bool from do
  let three := q(3)
  let mvar ← mkFreshExprMVar (some <| .const `Nat [])
  withNewMCtxDepth do
    isDefEq three mvar

#eval show MetaM Bool from do
  let three := q(3)
  withNewMCtxDepth do
    let mvar ← mkFreshExprMVar (some <| .const `Nat [])
    isDefEq three mvar

#eval show MetaM Bool from do
  let three ← mkFreshExprMVar (some <| .const `Nat []) -- read only
  withNewMCtxDepth do
    let mvar ← mkFreshExprMVar (some <| .const `Nat [])
    isDefEq three mvar

#eval show MetaM Bool from do
  let three ← mkFreshExprMVar (some <| .const `Nat [])
  let mvar ← mkFreshExprMVar (some <| .const `Nat [])
  withNewMCtxDepth do
    isDefEq three mvar

#eval show MetaM Bool from do
  let three := q(3)
  let three_also := q(3)
  withNewMCtxDepth do
    isDefEq three three_also
