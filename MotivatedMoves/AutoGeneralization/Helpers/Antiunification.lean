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

initialize
  registerTraceClass `AntiUnify

/-- Compute the least common generalizer of the given pair of expressions.
    The convention throughout is that the attributes of the first expression preferentially get copied over to the result whenever there is a choice. -/
partial def antiUnify (e e' : Expr) : StateT (List Mismatch) MetaM Expr := do
  trace[AntiUnify] m!"Anti-unifying {e} and {e'}"
  match e, e' with
  | .forallE n d b bi, .forallE n' d' b' bi' =>
    let dA ← antiUnify d d'
    withLocalDecl n bi dA fun var ↦ do
      let bA ← antiUnify (b.instantiate1 var) (b'.instantiate1 var)
      let mismatches ← get
      if mismatches.any fun ⟨_, left, right⟩ ↦ left.containsFVar var.fvarId! || right.containsFVar var.fvarId! then do
        throwError m!"Unsupported case: Loose free variable {var} in anti-unification."
      set mismatches
      return ← mkForallFVars #[var] bA
  | .lam n d b bi, .lam n' d' b' bi' =>
    let dA ← antiUnify d d'
    withLocalDecl n bi dA fun var ↦ do
      let bA ← antiUnify (b.instantiate1 var) (b'.instantiate1 var)
      let mismatches ← get
      if mismatches.any fun ⟨_, left, right⟩ ↦ left.containsFVar var.fvarId! || right.containsFVar var.fvarId! then do
        throwError m!"Unsupported case: Loose free variable {var} in anti-unification."
      set mismatches
      return ← mkLambdaFVars #[var] bA
  | .letE n d v b nd, .letE n' d' v' b' nd' =>
    -- it doesn't make sense to anti-unify `v` and `v'` unless `d = d'`
    unless ← liftM <| withoutModifyingState <| isDefEq d d' do
      throwError s!"Expected the domains of the two `let` declarations {e} and {e'} to be the same."
    let vA ← antiUnify v v'
    withLetDecl n d vA fun var ↦ do
      let bA ← antiUnify (b.instantiate1 var) (b'.instantiate1 var)
      let mismatches ← get
      if mismatches.any fun ⟨_, left, right⟩ ↦ left.containsFVar var.fvarId! || right.containsFVar var.fvarId! then do
        throwError m!"Unsupported case: Loose free variable {var} in anti-unification."
      set mismatches
      return ← mkLetFVars #[var] bA
  | .app f a, .app f' a' =>
    if ← liftM <| withoutModifyingState <| isDefEq (← inferType f) (← inferType f') then
      return .app (← antiUnify f f') (← antiUnify a a')
    else
      createAntiunifyingMVar
  | .proj n idx s, .proj n' idx' s' =>
    unless n = n' ∧ idx = idx' do
      throwError m!"Data of projections {e} and {e'} do not match."
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
    -- making `m` the placeholder if the assignment is consistent with previous mismatches
    else if (← get).all fun mismatch ↦ (mismatch.placeholder != m) || (mismatch.right == e') then
      modify <| List.cons { placeholder := m, left := .mvar m, right := e' }
      return .mvar m
    else
      createAntiunifyingMVar
  | e, .mvar m' =>
    if ← m'.isAssigned then
      return ← antiUnify e (← instantiateMVars (.mvar m'))
    -- making `m'` the placeholder if the assignment is consistent with previous mismatches
    else if (← get).all fun mismatch ↦ (mismatch.placeholder != m') || (mismatch.left == e) then
      modify <| List.cons { placeholder := m', left := e, right := .mvar m' }
      return .mvar m'
    else
      createAntiunifyingMVar
  | e, e' => createAntiunifyingMVar
where
  createAntiunifyingMVar : StateT (List Mismatch) MetaM Expr := do
    let t ← inferType e
    let t' ← inferType e'
    unless ← liftM <| withoutModifyingState <| isDefEq t t' do
      throwError m!"The types of mismatched terms {e} and {e'} do not align."
    if ← liftM <| withoutModifyingState <| isDefEq e e' then
      return e
    else
      trace[AntiUnify] m!"Creating anti-unifying metavariable for {e} and {e'} of type {t}"
      let mvar ← mkFreshExprMVar (some t)
      modify <| List.cons { placeholder := mvar.mvarId!, left := e, right := e' }
      return mvar

def leastCommonGeneralizer (e e' : Expr) : MetaM Expr :=
  antiUnify e e' |>.run' []

/-- `getTermsToGeneralize` takes in two expressions and gives the antiunification result together with a list of terms that are causing conflict in unification.
    The Boolean flag attached to each term indicates whether it has come from the left expression or the right (`false` for left, `true` for right). -/
def getTermsToGeneralize (e e' : Expr) : MetaM (Expr × List (Bool × Expr)) := do
  let (result, mismatches) ← antiUnify e e' |>.run []
  let conflicts ← mismatches.filterMapM fun ⟨_, left, right⟩ ↦ do
    let l ← getMVars left
    let r ← getMVars right
    if l.size < r.size then
      pure (false, left)
    else if r.size < l.size then
      pure (true, right)
    else
      pure none
  return (result, conflicts)

end AntiUnify
