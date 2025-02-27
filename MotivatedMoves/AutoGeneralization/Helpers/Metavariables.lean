import Lean
import MotivatedMoves.AutoGeneralization.Helpers.Subexpressions

open Lean Elab Tactic Meta Term Command

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

/-- Pull out mvars as hypotheses to create a chained implication-/
def pullOutMissingHolesAsHypotheses (proof : Expr) : MetaM Expr :=
  return (← abstractMVars proof).expr
