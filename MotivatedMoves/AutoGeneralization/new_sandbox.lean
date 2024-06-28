import Lean
import Mathlib.FieldTheory.Finite.Basic
import Qq

open Lean Elab Tactic Meta Term Command Qq

elab "test" : tactic => do

  let userSelected ← mkFreshExprMVarQ q(Nat)
  let userMVarId := userSelected.mvarId!
  let userSelectedAnnotated := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ .mvar userMVarId
  let e := mkLambda `x .default q(Nat) $ mkApp2 q(@HAdd.hAdd Nat Nat Nat instHAdd) userSelectedAnnotated q(3 + 3)
  let x ← mkFreshExprMVarQ q(Nat)
  let y ← mkFreshExprMVarQ q(Nat)
  let e' := mkLambda `x .default q(Nat) q($y + ($y + $x))
  logInfo m!"mvar e {e}"
  logInfo m!"mvar e' {e'}"
  logInfo m!"def eq {← isDefEq e' e }" -- the one that comes second is the one that gets its mvar borrowed in assignments
  -- let e' ← instantiateMVarsExcept userMVarId e'
  logInfo m!"instantiated e {e}"
  logInfo m!"instantiated e' {e'}"

example : True :=
  test
