/- Helper functions that make Lean 4 Metaprogramming a bit more intuitive. -/

import Lean
import Mathlib.Tactic
open Lean Elab Tactic Meta Term Command

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Retrieving the goal
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
/-- Return goal variable -/
def getGoalVar : TacticM MVarId := do
  return ← getMainGoal

/--  Return goal declaration-/
def getGoalDecl : TacticM MetavarDecl := do
  return ← getMainDecl -- (← getGoalVar).getDecl

/-- Return goal expression (the type) -/
def getGoalType : TacticM Expr := do
  return ← getMainTarget -- (← getGoalDecl).type or (← getGoalVar).getType

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Creating a goal
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
/-- Create a new goal -/
def createGoal (goalType : Expr) : TacticM Unit := do
  let goal ← mkFreshExprMVar goalType
  appendGoals [goal.mvarId!]

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Retrieving hypotheses
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
/--  Return hypotheses declarations (not including dynamically generated ones associated to the main goal) -/
def getInitialHypotheses : MetaM (List LocalDecl) := do
  let mut hypotheses : List LocalDecl := []
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses
elab "getInitialHypotheses": tactic => do {let hList ← getInitialHypotheses; for lDecl in hList do logInfo lDecl.userName}
example (P : Prop) (Q : Prop) := by {getInitialHypotheses; have R := True; getInitialHypotheses; assumption}

/--  Return hypotheses declarations associated to the main goal -/
def getHypotheses : TacticM (List LocalDecl) := withMainContext do
  let mut hypotheses : List LocalDecl := []
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses
elab "getHypotheses": tactic => do {let hList ← getHypotheses; for lDecl in hList do logInfo lDecl.userName}
example (P : Prop) (Q : Prop) := by {getHypotheses; have R := True; getHypotheses; assumption}

/--  Get a hypothesis declaration by its name -/
def getHypothesisByName (h : Name) : TacticM LocalDecl := do
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    if ldecl.userName == h then
      return ldecl
  throwError "No hypothesis by that name."

/-- Get the statement of a given hypothesis (given its name) -/
def getHypothesisType (h : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName h
  return hyp.type

/-- Get the proof of a given hypothesis (given its name) -/
def getHypothesisProof (h : Name) : TacticM Expr := do
  (← getMainGoal).withContext do
    let hyp ← getHypothesisByName h
    if hyp.hasValue
      then
        if hyp.value.isMVar
          then
            let val ← getExprMVarAssignment? hyp.value.mvarId! -- works if proved in tactic mode like `:= by ...`
            return ← liftOption val
          else return hyp.value -- works if proved directly with a proof term like `:= fun ...`
      else throwError "The hypothesis was likely declared with a 'have' rather than 'let' statement, so its proof is not accessible."

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Creating hypotheses
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Create a new hypothesis using a "have" statement -/
def createHaveHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  let hyp : Hypothesis := { userName := hypName, type := hypType, value := hypProof }
  let (_, new_goal) ← (←getGoalVar).assertHypotheses (List.toArray [hyp])
  setGoals [new_goal]

/-- Create a new hypothesis using a "let" statement (so its proof is accessible)-/
def createHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  let new_goal ← (←getGoalVar).define hypName hypType hypProof
  let (_, new_goal) ← new_goal.intro1
  setGoals [new_goal]

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Converting expressions to code (evaluation)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Converting code to expressions (elaboration)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
elab "#term_to_expr" t:term : command => do
  let e ← liftTermElabM (Term.elabTerm t none)
  logInfo m!"The expression corresponding to {t} is:\n\n{repr e}"
#term_to_expr (2+3=5)

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Checking types of expressions
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/--  Tactic to return T/F depending on the type of an expression -/
def isNat (e: Expr): MetaM Bool := do
  let type_expr ← inferType e
  return type_expr.isConstOf `Nat

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Printing expressions in varying degrees of detail
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- What the expression fully looks like --/
def logExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{repr e}"

/-- What the expression looks like, but with details hidden, so its prettier --/
def logPrettyExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{←ppExpr e}"

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Getting subexpressions
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- Get (in a list) all subexpressions in an expression -/
def getSubexpressionsIn (e : Expr) : MetaM (List Expr) :=
  let rec getSubexpressionsInRec (e : Expr) (acc : List Expr) : MetaM (List Expr) :=
    match e with
    | Expr.forallE _ d b _   => return [e] ++ (← getSubexpressionsInRec d acc) ++ (← getSubexpressionsInRec b acc)
    | Expr.lam _ d b _       => return [e] ++ (← getSubexpressionsInRec d acc) ++ (← getSubexpressionsInRec b acc)
    | Expr.letE _ t v b _    => return [e] ++ (← getSubexpressionsInRec t acc) ++ (← getSubexpressionsInRec v acc) ++ (← getSubexpressionsInRec b acc)
    | Expr.app f a           => return [e] ++ (← getSubexpressionsInRec f acc) ++ (← getSubexpressionsInRec a acc)
    | Expr.mdata _ b         => return [e] ++ (← getSubexpressionsInRec b acc)
    | Expr.proj _ _ b        => return [e] ++ (← getSubexpressionsInRec b acc)
    | _                      => return acc
  getSubexpressionsInRec e []

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Getting theorems declared in the context
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Getting theorem statement from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.type -- return the theorem statement

/-- Getting theorem proof from context --/
def getTheoremProof (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.value! -- return the theorem statement

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Getting metavariables in the context
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

def printMVarsAssignmentsInContext : MetaM Unit := do
  let m ← getMCtx
  logInfo m!"MVar Context:
    {(m.eAssignment.toList.map (fun d =>
    m!"Mvar:
      {d.fst.name}
    Assignment:
      {repr d.snd}"

  ))}"

def printMVarContext : MetaM Unit := do
  let m ← getMCtx
  logInfo m!"MVar Context: {(m.decls.toList.map (fun d =>
    m!"Name: {d.fst.name} Kind:{repr d.snd.kind} "
  ))}"

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Getting all variables and instances in local context
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/


def printLocalContext : MetaM Unit := do
  let (lctx, linst) := (← getLCtx, ← getLocalInstances)
  logInfo m!"Local context {lctx.decls.toList.filterMap (fun oplocdec => oplocdec.map (LocalDecl.userName))}"
  logInfo m!"Local instances {linst.map LocalInstance.className}"
