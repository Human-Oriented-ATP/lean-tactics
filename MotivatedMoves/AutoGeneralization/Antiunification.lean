import Lean

open Lean Meta Elab Tactic Command

/-!

# Anti-unification

**Input:** Two expressions `e` and `e'` of the same type
**Output:** The least common generalizer of `e` and `e'`
            (i.e., an expression with meta-variables that can be instantiated to either `e` or `e'`, and in fact, the most specific such one)
            along with a list of the "mismatches" between the two expressions
-/

namespace AntiUnify

set_option linter.unusedVariables false

/-- An `Expr.Mismatch` records the data of
    where two expressions being compared differ. -/
structure Mismatch where
  /-- The name of the meta-variable used in the least common generalizer. -/
  placeholder : MVarId
  left : Expr
  right : Expr
deriving Repr

/-- Compute the least common generalizer of the given pair of expressions.
    The convention throughout is that the attributes of the first expression preferentially get copied over to the result whenever there is a choice. -/
partial def antiUnify (e e' : Expr) : StateT (List Mismatch) MetaM Expr := do
  match e, e' with
  | .forallE n d b bi, .forallE n' d' b' bi' =>
    let dA ← antiUnify d d'
    withLocalDecl n bi dA fun var ↦ do
      let bA ← antiUnify (b.instantiate1 var) (b'.instantiate1 var)
      return .forallE n dA bA bi
  | .lam n d b bi, .lam n' d' b' bi' =>
    let dA ← antiUnify d d'
    withLocalDecl n bi dA fun var ↦ do
      let bA ← antiUnify (b.instantiate1 var) (b'.instantiate1 var)
      return .lam n dA bA bi
  | .letE n d v b nd, .letE n' d' v' b' nd' =>
    -- it doesn't make sense to anti-unify `v` and `v'` unless `d = d'`
    unless ← liftM <| withoutModifyingState <| isDefEq d d' do
      throwError "Expected the domains of the two `let` declarations to be the same."
    let vA ← antiUnify v v'
    withLetDecl n d vA fun var ↦ do
      let bA ← antiUnify b b'
      return .letE n d vA bA (bA.containsFVar var.fvarId!)
  | .app f a, .app f' a' =>
    return .app (← antiUnify f f') (← antiUnify a a')
  | .proj n idx s, .proj n' idx' s' =>
    unless n = n' ∧ idx = idx' do
      throwError "Data of projections do not match."
    return .proj n idx (← antiUnify s s')
  | .mdata md e, .mdata md' e' =>
    return .mdata (KVMap.mergeBy (fun _ d _ ↦ d) md md') (← antiUnify e e')
  | .mdata md e, e' =>
    return .mdata md (← antiUnify e e')
  | e, .mdata md' e' =>
    return .mdata md' (← antiUnify e e')
  | .mvar m, e' =>
    if ← m.isAssigned then
      return ← antiUnify (← instantiateMVars (.mvar m)) e'
    else
      modify <| List.cons { placeholder := m, left := .mvar m, right := e' }
      return .mvar m
  | e, .mvar m' =>
    if ← m'.isAssigned then
      return ← antiUnify e (← instantiateMVars (.mvar m'))
    else
      modify <| List.cons { placeholder := m', left := e, right := .mvar m' }
      return .mvar m'
  | e, e' =>
    let t ← inferType e
    let t' ← inferType e'
    unless ← liftM <| withoutModifyingState <| isDefEq t t' do
      throwError "The types of mismatched terms do not align."
    if ← liftM <| withoutModifyingState <| isDefEq e e' then
      return e
    else
      let mvar ← mkFreshExprMVar (some t)
      modify <| List.cons { placeholder := mvar.mvarId!, left := e, right := e' }
      return mvar

def leastCommonGeneralizer (e e' : Expr) : MetaM Expr :=
  antiUnify e e' |>.run' []

def getMismatches (e e' : Expr) : MetaM (List Mismatch) := do
  let (result, mismatches) ← antiUnify e e' |>.run []
  return mismatches

end AntiUnify
