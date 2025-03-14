import Lean
import MotivatedMoves.AutoGeneralization.Helpers.ReplacePatternWithMVars

open Lean Elab Tactic Meta Term Command


/-- Instantiate metavariables according to what unifies in a typecheck -/
def consolidateWithTypecheck (proof : Expr) : MetaM Expr := do
  try
    check proof
  catch e =>
    logInfo m!"Error: {e.toMessageData}"
    throwError "The type of the proof doesn't match the statement.  Perhaps a computation rule was used?"
  return ← instantiateMVars proof

/-- Re-specialize the occurrences of the pattern we are not interested in -/
def respecializeOccurrences (thmType : Expr) (genThmProof : Expr) (pattern : Expr) (occsToStayAbstracted : Occurrences) (consolidate : Bool) : MetaM Expr := do
  -- Get the occurrences of the pattern (in the theorem statement) the user wants to specialize
  let userThmType ← if consolidate then
    abstractToOneMVar thmType pattern occsToStayAbstracted
  else
    abstractToDiffMVars thmType pattern occsToStayAbstracted
  logInfo m!"!User Generalized Type: {userThmType}"

  -- Keep a record of mvars to keep track of
  let genThmType ← inferType genThmProof
  let mvarsInProof := (← getMVars genThmProof) ++ (← getMVars genThmType)

  -- Compare and unify mvars between user type and our generalized type
  let _ ← isDefEq  genThmType userThmType

  -- Instantiate the ones we don't want to generalize
  let userSelectedMVars ← getAllMVarsContainingMData mvarsInProof
  return ← instantiateMVarsExcept userSelectedMVars genThmProof
