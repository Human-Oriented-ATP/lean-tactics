import Mathlib.Tactic
import MotivatedMoves.Mirek.SmtHammer.Solver
import MotivatedMoves.Mirek.WindowProblem.Defs
import MotivatedMoves.Mirek.WindowProblem.WindowModel

open Qq

elab "test_tactic" : tactic => do
  let x := q(countWindow)
  match x with
  | .const name levels => do
    Lean.logInfo "Yay!"
    Lean.logInfo name
    Lean.logInfo "levels"
    for level in levels do
      Lean.logInfo level
  | _ => Lean.logInfo (toString x)

example : True := by
  test_tactic
  trivial

structure BoundsState where
  l : Option Q(List Bool)
  bounds : Std.HashSet Q(Int)
deriving Inhabited

abbrev BoundsStateM := StateT BoundsState Lean.Elab.Tactic.TacticM

partial
def collectBoundsTerm : SmtRichExpr → BoundsStateM Unit
| .list l => do
  for x in l do
    collectBoundsTerm x
| .atomic (.app (.app (.app (.const `countWindow _) l) a) b) _ =>
  modify (fun state => {
    l := some (match state.l with | some ll => ll | none => l)
    bounds := state.bounds.insertMany [a,b]
  })
| _ => pure ()

-- instantiated theorems based on found bounds
def exportBounds
: BoundsStateM (Array Q(Prop))
:= do
  let mut res : Array Q(Prop) := #[]
  let state ← get
  match state.l with
  | some l =>
    for x0 in state.bounds do
      for x1 in state.bounds do
        if x0 == x1 then continue
        let e := q(count_window_add0 $l $x0 $x1)
        res := res.push (← Lean.Meta.inferType e)
        let e := q(count_window_basic_bound $l $x0 $x1)
        res := res.push (← Lean.Meta.inferType e)
        let e := q(count_window_zero $l $x0 $x1)
        res := res.push (← Lean.Meta.inferType e)
      let e := q(count_window_zero0 $l $x0)
      res := res.push (← Lean.Meta.inferType e)
    return res
  | none => return #[]

inductive WindowSolverOutput
| unsat
| unknown
| model (m : WindowModel)

def WindowSolverOutput.fromSolverOutput (b : BoundsState)
: SolverOutput → Lean.Meta.MetaM WindowSolverOutput
| .unsat => return .unsat
| .unknown => return .unknown
| .model m => match b.l with
  | none => return .unknown
  | some l => do
    let varValues := m.intsL.filter (fun (e,_) => e.isFVar)
    let bounds ← b.bounds.toList.mapM (fun bound => do
      let value ← m.intValue bound
      return (value, bound)
    )
    let bounds := bounds.mergeSort (fun (v1,_) (v2,_) => v1 < v2)
    let bounds := bounds.groupBy (fun (v1,_) (v2,_) => v1 == v2)
    let bounds := bounds.map (fun group =>
      let (value,_) := group.head!
      (value, group.map Prod.snd)
    )
    let blocks ← (bounds.zip bounds.tail).mapM (
      fun ((v1,bs1),(v2,bs2)) => do
      let b1 := bs1.head!
      let b2 := bs2.head!
      let e : Q(Nat) := q(countWindow $l $b1 $b2)
      match m.intsD.get? e with
      | some c => return (c.toNat, (v2-v1).toNat)
      | none => do
        let eStr ← Lean.Meta.ppExpr e
        throwError s!"fromSolverOutput: Expression not covered by the model: {eStr}"
    )
    let varValuesStr ← varValues.mapM (
      fun (e, val) => do
      return (toString (←Lean.Meta.ppExpr e), val)
    )
    let boundsStr ← bounds.mapM (
      fun (val, bs) =>
      return (val, ←bs.mapM (
        fun e => do
        return toString (←Lean.Meta.ppExpr e)
      ))
    )
    let wm : WindowModel := {
      varValues := varValuesStr
      bounds := boundsStr
      blocks := blocks
    }
    return .model wm

def windowTactic (stx : Lean.Syntax) : Lean.Elab.Tactic.TacticM Unit
:= Lean.Elab.Tactic.withMainContext do
  let rich1 ← stateToRichSmt
  let cmd : BoundsStateM (Array Q(Prop)) := do
    for x in rich1 do
      collectBoundsTerm x
    exportBounds
  let (boundThms, bounds) ← StateT.run cmd default
  let rich2 ← boundThms.filterMapM (fun e : Lean.Expr => do
    SmtRichExpr.fromLeanProp? e
  )
  let (smtLines, ctx) := richToSmt (rich1++rich2)
  let solverOutputRaw : SolverOutputRaw ← runSolver smtLines
  let solverOutput : SolverOutput
    := StateT.run' (solverOutputRaw.toLean) ctx
  match ←WindowSolverOutput.fromSolverOutput bounds solverOutput with
  | .unsat =>
    Lean.Elab.Tactic.evalTactic <| ← `(tactic | int_hammer_sorry)
  | .unknown =>
    Lean.logInfo "Cannot extract a model"
  | .model m =>
    -- Lean.logInfo (← m.toString)
    m.showHtml stx

elab stx:"window_tactic" : tactic => do
  windowTactic stx
