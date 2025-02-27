import Lean
open Lean Elab Tactic Meta Term Command

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Working with names
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

def placeholderName := `placeholder
def preferredNames := #[`n, `m, `p, `a, `b, `c]

/-- Relabel the metavariables in the expression with their preferred names. -/
def relabelMVarsIn (e : Expr) : MetaM Unit := do
  let mvars ← getMVars e
  let placeholderMVars ← mvars.filterM fun mvar => do
   return (← mvar.getTag).getRoot.toString.startsWith placeholderName.toString
  for (mvar, name) in placeholderMVars.zip preferredNames do
      mvar.setUserName name


/-- Turn a lemma name into its generalized version by prefixing it with `gen_` and truncating. -/
def mkAbstractedName (n : Name) : Name :=
    match n with
    | (.str _ s) =>  Name.mkSimple s!"gen_{s.takeWhile (fun c => c != '_')}" -- (fun c => c.isLower && c != '_')
    | _ => `unknown
