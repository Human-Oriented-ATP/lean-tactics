import Lean
open Lean Elab Tactic Meta Term Command



/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Retrieving the goal
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--  Tactic to return goal variable -/
def getGoalVar : TacticM MVarId := do
  return ← getMainGoal

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Retrieving hypotheses
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Getting theorem statement from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | throwError "No theorem of that name was found."
 -- get the declaration with that name
  return thm.type -- return the theorem statement

/-- Getting theorem proof from context --/
def getTheoremProof (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | throwError "No theorem of that name was found."
  return thm.value! -- return the theorem statement

/-- Get a hypothesis by its name -/
def getHypothesisByName (h : Name) : TacticM LocalDecl := do
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    if ldecl.userName == h then
      return ldecl
  throwError m!"No hypothesis by name '{h}'."

/-- Get the statement of a given hypothesis (given its name) -/
def getHypothesisType (h : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName h
  return hyp.type

/-- Get the proof of a given hypothesis (given its name) -/
def getHypothesisProof (h : Name) : TacticM Expr := do
  (← getMainGoal).withContext do
    let hyp ← getHypothesisByName h

    if hyp.hasValue
      then return ← instantiateMVars hyp.value
      else throwError "The hypothesis was likely declared with a 'have' rather than 'let' statement, so its proof is not accessible."

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Creating hypotheses
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Create a new hypothesis using a "let" statement (so its proof is accessible)-/
def createLetHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  let check ← isDefEq (hypType) (← inferType hypProof)
  if !check then throwError "Hypothesis type {hypType} doesn't match proof {hypProof}"
  let new_goal ← (←getGoalVar).define hypName hypType hypProof
  let (_, new_goal) ← intro1Core new_goal true
  setGoals [new_goal]


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
 -- | Expr.letE _ t v b _    => [e] ++ (← getSubexpressionsInRec t acc) ++ (← getSubexpressionsInRec v acc) ++ (← getSubexpressionsInRec b acc)
    | Expr.app f a           => return [e] ++ (← getSubexpressionsInRec f acc) ++ (← getSubexpressionsInRec a acc)
    | Expr.mdata _ b         => return [e] ++ (← getSubexpressionsInRec b acc)
    | Expr.proj _ _ b        => return [e] ++ (← getSubexpressionsInRec b acc)
    | Expr.mvar _            => return [e] ++ acc
    | Expr.bvar _            => return [e] ++ acc
    | _                      => return [e] ++ acc
  let subexprs ← (getSubexpressionsInRec e [])
  --logInfo m!"subexprs before bvar filter {subexprs}"
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

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Working with metavariables
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Remove the assignment of a metavariable from the context. -/
def removeAssignment (mv : MVarId) : MetaM Unit := do
  -- remove the assignment
  let mctx ← getMCtx
  let mctxassgn := mctx.eAssignment.erase mv
  setMCtx {mctx with eAssignment := mctxassgn} -- mctxassgn

/-- Instantiates all mvars in e except the mvar given by the array a -/
def instantiateMVarsExcept (a : Array MVarId) (e : Expr)  : MetaM Expr := do
  for mv in a do
   removeAssignment mv -- remove the assignment
  let e ← instantiateMVars e -- instantiate mvars
  return e

/-- Returns the assignment of metavariable `m` -/
def getAssignmentFor (m : MVarId) : MetaM (Option Expr) := do
  let e ← getExprMVarAssignment? m
  return e

/-- Returns true if the expression contains metadata -/
def containsMData (e : Expr): MetaM Bool := do
  return ← containsExprWhere (Expr.isMData) e


/-- Returns true if the expression is assigned to another expression containing metadata -/
def assignmentContainsMData (m : MVarId) : MetaM Bool := do
  let m_assignment ← getAssignmentFor m
  if let some assignment := m_assignment then
    if ← containsMData assignment then
      return True
  return False

/-- Returns a list of all metavariables whose assignment contains metadata -/
def getAllMVarsContainingMData (a : Array MVarId): MetaM (Array MVarId) :=
   a.filterM assignmentContainsMData
