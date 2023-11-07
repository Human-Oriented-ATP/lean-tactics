import Lean 
import MotivatedMoves.ProofState.Tree
import MotivatedMoves.ProofState.ExhaustPositions
import Mathlib.Tactic.Linarith.Preprocessing

open Lean Elab Tactic Meta 

def runTacticInSandbox (tactic : TacticM Unit) : TacticM $ Option Expr := do
  let initialState ← saveState
  if ← tryTactic tactic then
    if (← getGoals).isEmpty then 
      pure none
    else
      let newProofState ← getMainTarget
      initialState.restore
      pure newProofState
  else 
    pure none

def orList : List Prop → Prop 
  | [] => False
  | [x] => x 
  | x :: xs => Or x (orList xs)

def determineNewTarget (tactic : α → TacticM Unit) (validParameters : Array α) : TacticM Expr := do 
  let newProofStates ← validParameters.filterMapM (fun a => runTacticInSandbox (tactic a))
  let newProofStatesWithoutDuplicates := @Array.sortAndDeduplicate _ Linarith.Expr.Ord newProofStates
  let newProofStatesList ← mkListLit (.sort .zero) newProofStatesWithoutDuplicates.toList
  let newTarget ← mkAppM ``orList #[newProofStatesList]
  pure newTarget 

def mkMVarOfType (type : Expr) : TacticM MVarId := do 
  let newMVarId ← mkFreshMVarId
  let _ ← mkFreshExprMVarWithId newMVarId (some type)
  pure newMVarId

def simplifyOrList : TacticM Unit := do 
  evalTactic (←`(tactic|simp only [orList]))

def exhaustParametricTacticUnsound (tactic : α → TacticM Unit) (validParameters : Array α) : TacticM Unit := do
  let goal ← getMainGoal 
  let newTarget ← determineNewTarget tactic validParameters
  if (← getGoals).isEmpty then 
    pure ()
  else 
    let newMVarId ← mkMVarOfType newTarget
    appendGoals [newMVarId]
    admitGoal goal
    simplifyOrList

def exhaustParametricTacticOnAllPositions (tactic : (List Nat) → TacticM Unit) : TacticM Unit := do
  let target ← getMainTarget
  let allPositions ← getValidPositions target
  exhaustParametricTacticUnsound tactic allPositions

def exhaustParametricTacticOnAllPositions2 
  (tactic : (List Nat × List Nat) → TacticM Unit) : TacticM Unit := do
  let target ← getMainTarget
  let allPositions ← getValidPositions target
  let allPositions2 := allPositions.map (fun fst => allPositions.map (fun snd => (fst, snd))) 
  exhaustParametricTacticUnsound tactic allPositions2.flatten

-- TESTS: 

def myTactic (n : Nat) : TacticM Unit := do 
  match n with 
  | 0 => dbg_trace "Case 0: Error" 
         throwError "Ouch!"
  | 1 => dbg_trace "Case 1: Nothing"
         pure ()
  | 2 => dbg_trace "Case 2: Simp"
         evalTactic (← `(tactic|simp))
  | _ => dbg_trace "Case >=3: Nothing"
         pure ()

elab "testExhaust" : tactic => do 
  exhaustParametricTacticUnsound myTactic #[0, 1]

example : 1+1 = 2 := by 
  testExhaust
