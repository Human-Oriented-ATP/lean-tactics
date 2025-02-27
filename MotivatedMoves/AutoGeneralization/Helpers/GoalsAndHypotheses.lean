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
