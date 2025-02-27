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
def getHypothesisByName (n : Name) : TacticM LocalDecl := do
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    if ldecl.userName == n then
      return ldecl
  throwError m!"No hypothesis by name '{n}' was found."

/-- Get the statement of a given hypothesis (given its name) -/
def getHypothesisType (n : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName n
  return hyp.type

/-- Get the proof of a given hypothesis (given its name) -/
def getHypothesisProof (n : Name) : TacticM Expr := do
  (← getMainGoal).withContext do
    let hyp ← getHypothesisByName n

    if hyp.hasValue
      then return ← instantiateMVars hyp.value
      else throwError "The hypothesis was likely declared with a 'have' rather than 'let' statement, so its proof is not accessible."

/-- Get the specifying theorem from a local hypothesis if that exists, and otherwise from the environment -/
def getTheoremAndProof (thmName : Name) : TacticM (Expr × Expr) := do
  try return (← getHypothesisType thmName, ← getHypothesisProof thmName) -- if the theorem is a hypothesis of the current proof state
  catch _ => return (← getTheoremStatement thmName, ← getTheoremProof thmName) -- if the theorem is in the environment

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


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Working with metavariables
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Remove the assignment of a metavariable from the context. -/
def removeAssignment (mv : MVarId) : MetaM Unit := do
  -- remove the assignment
  let mctx ← getMCtx
  let mctxassgn := mctx.eAssignment.erase mv
  setMCtx {mctx with eAssignment := mctxassgn} -- mctxassgn

/-- Instantiates all mvars in e except the mvars given by the array a -/
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

/-- Returns true if given an expression `e` has a metavariable of type `t`-/
def hasMVarOfType (t e: Expr) : MetaM Bool := do
  let mvarIds ← getMVars e
  mvarIds.anyM (fun m => do withoutModifyingState (isDefEq (← m.getType') t))

/-- Make all mvars in mvarArray with the type t the same  -/
def setEqualAllMVarsOfType (mvarArray : Array MVarId) (t : Expr) : MetaM Unit := do
  let m ← mkFreshExprMVar t -- new mvar to replace all others with the same type
  for mv in mvarArray do
    if ← isDefEq (← mv.getType) t then
      if !(← mv.isAssigned) then mv.assign m--mv.assignIfDefeq m
