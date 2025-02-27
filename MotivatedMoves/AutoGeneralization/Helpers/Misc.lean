import Lean
open Lean Elab Tactic Meta Term Command


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Working with names
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Turn a lemma name into its generalized version by prefixing it with `gen_` and truncating. -/
def mkAbstractedName (n : Name) : Name :=
    match n with
    | (.str _ s) =>  Name.mkSimple s!"gen_{s.takeWhile (fun c => c != '_')}" -- (fun c => c.isLower && c != '_')
    | _ => `unknown

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Working with function applications
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Returns the argument to an expression e.g. if fAbs has type "n-1= 3 → n=4" then it returns "n-1=3"-/
def extractArgType (fAbs : Expr) : MetaM Expr := do
  let fAbsType ← inferType fAbs
  return fAbsType.bindingDomain!
