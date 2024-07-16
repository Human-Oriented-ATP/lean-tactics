/- Helper functions that make Lean 4 Metaprogramming a bit more intuitive. -/

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
example (P : Prop) (Q : Prop) := by
  getInitialHypotheses;
  have R := True; getInitialHypotheses; assumption

/--  Return hypotheses declarations associated to the main goal -/
def getHypotheses : TacticM (List LocalDecl) := withMainContext do
  let mut hypotheses : List LocalDecl := []
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses
elab "getHypotheses": tactic => do {let hList ← getHypotheses; for lDecl in hList do logInfo lDecl.userName}
example (P : Prop) (Q : Prop) := by
  getHypotheses;
  have R := True; getHypotheses; assumption

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
def createLetHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  let new_goal ← (←getGoalVar).define hypName hypType hypProof
  let (_, new_goal) ← new_goal.intro1
  setGoals [new_goal]

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
#eval (q(2+3=5) : Expr)     -- create expressions
#check (Q(Nat) : Type)      -- create types
#eval (q(3) : Q(Nat))       -- create an expression of a certain type
#eval (q(2+3=5) : Q(Prop))  -- create an expression of another type

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Checking types of expressions
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Tells you how an expression was constructed (for debugging purposes) -/
def getExprConstructor (e: Expr): MetaM String := do
  return e.ctorName
#eval getExprConstructor (.bvar 0)      -- bvar
#eval getExprConstructor (.const `n []) -- const

/-- Tells you if an expression is a Float (for debugging purposes) -/
def isFloat (e: Expr): MetaM Bool := do
  let type_expr ← inferType e
  return type_expr.isConstOf `Float
#eval isFloat (q(3))    -- false
#eval isFloat (q(3.3))  -- true

/-- Tells you if an expression is a Nat (for debugging purposes) -/
def isNat (e: Expr): MetaM Bool := do
  let type_expr ← inferType e
  return type_expr.isConstOf `Nat
#eval isNat (q(3))    -- true
#eval isNat (q(3.3))  -- false

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Printing expressions in varying degrees of detail
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Print what the expression fully looks like (compatible with #eval, unlike logInfo) --/
def logExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{repr e}"
#eval logExpression (toExpr 2)

/-- What the expression looks like, but with details hidden, so its prettier (compatible with #eval, unlike logInfo) --/
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

/-- Get (in a list) all subexpressions in an expression -/
def getSubexpressionsIn (e : Expr) : List Expr :=
  let rec getSubexpressionsInRec (e : Expr) (acc : List Expr) : List Expr :=
    match e with
    | Expr.forallE _ d b _   => [e] ++ (getSubexpressionsInRec d acc) ++ (getSubexpressionsInRec b acc)
    | Expr.lam _ d b _       => [e] ++ (getSubexpressionsInRec d acc) ++ (getSubexpressionsInRec b acc)
    | Expr.letE _ t v b _    => [e] ++ (getSubexpressionsInRec t acc) ++ (getSubexpressionsInRec v acc) ++ (getSubexpressionsInRec b acc)
    | Expr.app f a           => [e] ++ (getSubexpressionsInRec f acc) ++ (getSubexpressionsInRec a acc)
    | Expr.mdata _ b         => [e] ++ (getSubexpressionsInRec b acc)
    | Expr.proj _ _ b        => [e] ++ (getSubexpressionsInRec b acc)
    | Expr.mvar _            => [e] ++ acc
    | Expr.bvar _            => [e] ++ acc
    | e                      => [e] ++ acc
  let subexprs := getSubexpressionsInRec e [];
  let subexprs := subexprs.filter $ fun subexpr => !subexpr.hasLooseBVars -- remove the ones with loose bvars (will cause PANIC when using isDefEq)
  subexprs
#eval do {let e ← getTheoremStatement ``Nat.add_comm; for subexpr in (getSubexpressionsIn e) do logPrettyExpression subexpr}
#eval do {let e := q(∀a,a+a=2*a); for subexpr in (getSubexpressionsIn e) do logPrettyExpression subexpr}

/-- Returns true if "e" contains "subexpr".  Differs from "occurs" because this uses the coarser "isDefEq" rather than "==" -/
def containsExpr(subexpr : Expr)  (e : Expr) : MetaM Bool := do
  let mctx ← getMCtx -- save metavar context before using isDefEq
  let e_subexprs := getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return ← isDefEq e_subexpr subexpr)
  setMCtx mctx -- revert metavar context after using isDefEq, so this function doesn't have side-effects on the expr e
  return firstExprContainingSubexpr.isSome
#eval containsExpr (q(2)) q(∀a,a+a=2*a) -- true
#eval containsExpr (q(3)) q(∀a,a+a=2*a) -- false

/-- Returns all subexpressions in "e" where "condition" holds -/
def containsExprWhere (condition : Expr → MetaM Bool) (e : Expr)   : MetaM Bool := do
  let e_subexprs := getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return ← condition e_subexpr)
  return firstExprContainingSubexpr.isSome
#eval containsExprWhere isNat   q(∀a,a+a=2*a)   -- true
#eval containsExprWhere isFloat q(∀a,a+a=2*a)   -- false

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Replacing subexpressions
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Replaces all subexpressions in "e" definitionally equal to "original" with a bound variable -/
def replaceWithBVar (original : Expr) (e : Expr) : MetaM Expr :=
  return ← kabstract e original
#eval do logPrettyExpression $ ← replaceWithBVar (q(2)) (q(2+3=5)) -- replace "2" with a bvar in "2+3=5"

/-- Replaces all subexpressions in "e" definitionally equal to "original" with "replacement" -/
def replace (original : Expr) (replacement : Expr)  (e : Expr) : MetaM Expr := do
  let abstractedExpr ← kabstract e original
  return abstractedExpr.instantiate1 replacement
#eval do logPrettyExpression $ ← replace  (q(2)) (q(999)) (q(2+3=5))-- replace "2" with a "999" in "2+3=5"

/-- Replaces all subexpressions in "e" definitionally equal to "original" with a variable of type "replacementType" -/
def replaceWithMVar (original : Expr) (replacementType : Expr)  (e : Expr) : MetaM Expr := do
  let replacement ← mkFreshExprMVar replacementType
  replace original replacement e
#eval do logPrettyExpression $ ← replaceWithMVar  (q(2)) (.const `Nat []) (q(2+3=5))-- replace "2" with a "999" in "2+3=5"

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Getting metavariables in the context
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
/-- Returns all metavariable names and types in the context -/
def printMVarContext : MetaM Unit := do
  let m ← getMCtx
  dbg_trace "MVar Context:"
  for d in m.decls do
    let mvarId := d.fst
    let mvarDecl := d.snd
    dbg_trace s!"\tName: {mvarId.name} \n\tUserName: {mvarDecl.userName} \n\tType: {mvarDecl.type}\n"
#eval do
  let _ ← mkFreshExprMVarQ q(Nat) (userName := `hole0);let hole1 ← mkFreshExprMVarQ q(Nat) (userName := `hole1);let hole2 ← mkFreshExprMVarQ q(Nat) (userName := `hole2);let _ ← isDefEq q($hole1+3) q(2+$hole2)
  printMVarContext

/-- Returns all ASSIGNED metavariable names and types -/
def printMVarAssignments : MetaM Unit := do
  let m ← getMCtx
  dbg_trace "MVar Assingnments:"
  for d in m.eAssignment do
    let mvarId := d.fst
    let assignment := d.snd
    dbg_trace s!"\tName: {mvarId.name} \n\tAssignment: {← ppExpr assignment}\n"
#eval do
  let _ ← mkFreshExprMVarQ q(Nat) (userName := `hole0);let hole1 ← mkFreshExprMVarQ q(Nat) (userName := `hole1);let hole2 ← mkFreshExprMVarQ q(Nat) (userName := `hole2);let _ ← isDefEq q($hole1+3) q(2+$hole2)
  printMVarAssignments

/-- Returns the expression that an mvar has been assigned to (if it has been assigned) -/
def getAssignmentFor (m : MVarId) : MetaM (Option Expr) := do
  let e ← getExprMVarAssignment? m
  return e
#eval do
  let _ ← mkFreshExprMVarQ q(Nat) (userName := `hole0);let hole1 ← mkFreshExprMVarQ q(Nat) (userName := `hole1);let hole2 ← mkFreshExprMVarQ q(Nat) (userName := `hole2);let _ ← isDefEq q($hole1+3) q(2+$hole2)
  getAssignmentFor hole1.mvarId!

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Getting all variables and instances in local context
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Print local declarations (e.g. hypotheses) and local instances (e.g. typeclasses)-/
def printLocalContext : MetaM Unit := do
  let (lctx, linst) := (← getLCtx, ← getLocalInstances)
  logInfo s!"Local context {lctx.decls.toList.filterMap (fun oplocdec => oplocdec.map (LocalDecl.userName))}"
  logInfo s!"Local instances {linst.map LocalInstance.className}"
elab "printLocalContext": tactic => printLocalContext
example (P : Prop) [Decidable P]:= by {printLocalContext; assumption}
