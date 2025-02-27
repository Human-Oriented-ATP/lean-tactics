import Lean
open Lean Elab Tactic Meta Term Command


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Working with function applications
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Returns the argument to an expression e.g. if fAbs has type "n-1= 3 → n=4" then it returns "n-1=3"-/
def extractArgType (fAbs : Expr) : MetaM Expr := do
  let fAbsType ← inferType fAbs
  return fAbsType.bindingDomain!
