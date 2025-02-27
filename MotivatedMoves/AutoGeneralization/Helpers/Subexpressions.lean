import Lean
open Lean Elab Tactic Meta Term Command

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Working with subexpressions
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Get (in a list) all subexpressions in an expression -/
partial def getSubexpressionsIn (e : Expr) : MetaM (List Expr) := do
  let rec getSubexpressionsInRec (e : Expr) (acc : List Expr) : MetaM (List Expr) :=
    match e with
    | Expr.forallE n d b bi   => do
                                  let d_subexprs ← getSubexpressionsInRec d acc
                                  withLocalDecl n bi d (fun placeholder => do
                                    let b := b.instantiate1 placeholder
                                    let b_subexprs ← getSubexpressionsInRec b acc -- now it's safe to recurse on b (no loose bvars)
                                    let b_subexprs ← b_subexprs.mapM (fun s => mkForallFVars #[placeholder] s (binderInfoForMVars := bi)) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                                    return [e] ++ d_subexprs ++ b_subexprs
                                  )
    | Expr.lam n d b bi       => do
                                  let d_subexprs ← getSubexpressionsInRec d acc
                                  withLocalDecl n bi d (fun placeholder => do
                                    let b := b.instantiate1 placeholder
                                    let b_subexprs ← getSubexpressionsInRec b acc -- now it's safe to recurse on b (no loose bvars)
                                    let b_subexprs ← b_subexprs.mapM (fun s => mkLambdaFVars #[placeholder] s (binderInfoForMVars := bi))
                                    return [e] ++ d_subexprs ++ b_subexprs
                                  )
    | Expr.letE _ t v b _    => return [e] ++ (← getSubexpressionsInRec t acc) ++ (← getSubexpressionsInRec v acc) ++ (← getSubexpressionsInRec b acc)
    | Expr.app f a           => return [e] ++ (← getSubexpressionsInRec f acc) ++ (← getSubexpressionsInRec a acc)
    | Expr.mdata _ b         => return [e] ++ (← getSubexpressionsInRec b acc)
    | Expr.proj _ _ b        => return [e] ++ (← getSubexpressionsInRec b acc)
    | Expr.mvar _            => return [e] ++ acc
    | Expr.bvar _            => return [e] ++ acc
    | _                      => return [e] ++ acc
  let subexprs ← (getSubexpressionsInRec e [])
  let subexprs := subexprs.filter $ fun subexpr => !subexpr.hasLooseBVars -- remove the ones that will cause errors when parsing
  return subexprs

/-- Returns true if "e" contains "subexpr".  Differs from "occurs" because this uses the coarser "isDefEq" rather than "==" -/
def containsExpr(subexpr : Expr)  (e : Expr) : MetaM Bool := do
  let e_subexprs ← getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => withoutModifyingState (isDefEq e_subexpr subexpr))
  return firstExprContainingSubexpr.isSome

/-- Replaces all subexpressions where "condition" holds with the "replacement" in the expression e -/
def containsExprWhere (condition : Expr → Bool) (e : Expr)   : MetaM Bool := do
  let e_subexprs ← getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return condition e_subexpr)
  return firstExprContainingSubexpr.isSome
