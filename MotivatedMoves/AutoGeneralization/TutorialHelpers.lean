/- Helper functions that make Lean 4 Metaprogramming a bit more intuitive. -/

import Lean
import Mathlib.Tactic
import Qq open Qq
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

/-- Get the FVarID for a hypothesis (given its name) -/
def getHypothesisFVarId (h : Name) : TacticM FVarId := do
  let hyp ← getHypothesisByName h
  return hyp.fvarId

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

/-- Turn Lean syntax into an expression --/
def syntaxToExpr (e : TermElabM Syntax) : TermElabM Expr := do
  let e ← elabTermAndSynthesize (← e) none
  return e
#eval syntaxToExpr `(2+3=5)

/-- Print Lean terms as an expression --/
elab "#term_to_expr" t:term : command => do
  let e ← liftTermElabM (Term.elabTerm t none)
  logInfo m!"{repr e}"
#term_to_expr (2+3=5)

/- - Turn Lean terms into an expression, using Qq -/
#eval (q(2+3=5) : Expr)

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Checking types of expressions
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Tells you how an expression was constructed (for debugging purposes) -/
def getExprConstructor (e: Expr): MetaM String := do
  return e.ctorName
#eval getExprConstructor (.bvar 0)      -- bvar
#eval getExprConstructor (.const `n []) -- const

/-- Tells you if an expression is a Nat (for debugging purposes) -/
def isNat (e: Expr): MetaM Bool := do
  let type_expr ← inferType e
  return type_expr.isConstOf `Nat
#eval isNat (q(3))    -- true
#eval isNat (q(3.3))  -- false

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Printing expressions in varying degrees of detail
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- What the expression fully looks like --/
def logExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{repr e}"
#eval logExpression (toExpr 2)

/-- What the expression looks like, but with details hidden, so its prettier --/
def logPrettyExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{←ppExpr e}"
#eval logPrettyExpression (toExpr 2)

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Getting theorems declared in the context
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
/-- Getting theorem statement from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.type -- return the theorem statement
#eval do {let e ← getTheoremStatement ``Nat.add_comm; logPrettyExpression e}

/-- Getting theorem proof from context --/
def getTheoremProof (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.value! -- return the theorem statement
#eval do {let e ← getTheoremProof ``Nat.add_comm; logPrettyExpression e}


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
#eval do {let e ← getTheoremStatement ``Nat.add_comm; for subexpr in (← getSubexpressionsIn e) do logPrettyExpression subexpr}

/-- Returns true if "e" contains "subexpr".  Differs from "occurs" because this uses the coarser "isDefEq" rather than "==" -/
def containsExpr(subexpr : Expr)  (e : Expr) : MetaM Bool := do
  let mctx ← getMCtx -- save metavar context before using isDefEq
  let e_subexprs ← getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return ← isDefEq e_subexpr subexpr)
  setMCtx mctx -- revert metavar context after using isDefEq, so this function doesn't have side-effects on the expr e
  return firstExprContainingSubexpr.isSome

/- Returns all subexpressions where "condition" holds -/
def containsExprWhere (condition : Expr → Bool) (e : Expr)   : MetaM Bool := do
  let e_subexprs ← getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return condition e_subexpr)
  return firstExprContainingSubexpr.isSome

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Replacing subexpressions
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- Replaces all subexpressions in "e" definitionally equal to "original" with a bound variable -/
def replaceWithBVar (original : Expr) (e : Expr) : MetaM Expr :=
  return ← kabstract e original
#eval do logPrettyExpression $ ← replaceWithBVar (q(2)) (q(2+3=5)) -- replace "2" with a bvar in "2+3=5"

/- Replaces all subexpressions in "e" definitionally equal to "original" with "replacement" -/
def replaceWith (original : Expr) (replacement : Expr)  (e : Expr) : MetaM Expr := do
  let abstractedExpr ← kabstract e original
  return abstractedExpr.instantiate1 replacement
#eval do logPrettyExpression $ ← replaceWith  (q(2)) (q(3)) (q(2+3=5))-- replace "2" with a "3" in "2+3=5"

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Getting metavariables in the context
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/


/-- Returns all metavariable names and types in the context -/
def printMVarContext : MetaM Unit := do
  let m ← getMCtx
  logInfo m!"MVar Context: {(m.decls.toList.map (fun d =>
    let mvarId := d.fst
    let mvarDecl := d.snd
    m!"Name: {mvarId.name} Type: {mvarDecl.type}"
  ))}"

/-- Returns all ASSIGNED metavariable names and types -/
def printMVarsAssignmentsInContext : MetaM Unit := do
  let m ← getMCtx
  logInfo m!"MVar Assignments: {(m.eAssignment.toList.map (fun d =>
    m!"Mvar: {d.fst.name} Assignment: {d.snd}"
  ))}"

/-- Returns the expression that an mvar has been assigned to (if it has been assigned) -/
def getAssignmentFor (m : MVarId) : MetaM (Option Expr) := do
  let e ← getExprMVarAssignment? m
  return e
/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Getting all variables and instances in local context
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

def printLocalContext : MetaM Unit := do
  let (lctx, linst) := (← getLCtx, ← getLocalInstances)
  logInfo m!"Local context {lctx.decls.toList.filterMap (fun oplocdec => oplocdec.map (LocalDecl.userName))}"
  logInfo m!"Local instances {linst.map LocalInstance.className}"
