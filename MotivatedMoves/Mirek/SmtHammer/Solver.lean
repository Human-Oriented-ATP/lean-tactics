import MotivatedMoves.Mirek.SmtHammer.SmtExpr
import MotivatedMoves.Mirek.SmtHammer.SmtModel
import MotivatedMoves.Mirek.SmtHammer.SmtRichExpr
import MotivatedMoves.Mirek.SmtHammer.Parse

open Qq

def stateToRichSmt : Lean.Elab.Tactic.TacticM (Array SmtRichExpr)
:= Lean.Elab.Tactic.withMainContext do
  let mut res : Array SmtRichExpr := #[]
  for odecl in (← Lean.MonadLCtx.getLCtx).decls do
    match odecl with
    | some decl => do
      if decl.kind != default then continue
      match ←SmtRichExpr.fromLeanProp? decl.type with
      | some x => do
        res := res.push x
      | none => pure ()
    | none => pure ()
  match ←SmtRichExpr.fromLeanProp? (← Lean.Elab.Tactic.getMainTarget) with
  | some x => do
    res := res.push (.apply "not" [x])
  | none => pure ()
  return res

#check SmtNamesM.runEmpty

def richToSmt (richConstraints : Array SmtRichExpr) : Array SmtExpr × SmtNames
:= SmtNamesM.runEmpty do
  let constraints : Array SmtExpr ←
    richConstraints.mapM (fun rich => do
      let basic ← SmtNamesM.richToSmt rich
      return (.assert basic)
    )
  return (← SmtNamesM.exportTypes) ++ constraints

def stateToSmt : Lean.Elab.Tactic.TacticM (Array SmtExpr × SmtNames)
:= richToSmt <$> stateToRichSmt

inductive SolverOutputRaw
| unsat
| unknown
| model (e : SmtExpr)

inductive SolverOutput
| unsat
| unknown
| model (model : SmtModel)

def SolverOutputRaw.toLean : (raw : SolverOutputRaw) → SmtNamesM SolverOutput
| .unsat => return .unsat
| .unknown => return .unknown
| .model modelRaw => do
  let ctx ← get
  let mut ints : Array (Lean.Expr × Int) := #[]
  let mut bools : Array (Lean.Expr × Bool) := #[]
  match modelRaw with
  | .list l => do
    for assignment in l do
    -- ((define-fun x0 () Int 3) (define-fun x1 () Int 2))
      match assignment with
      | (.list [(.str "define-fun"), (.str name), (.list []), (.str t), valueRaw]) =>
        match ctx.nameToExpr.get? name with
        | some e =>
          match t with
          | "Bool" =>
            let value? : Option Bool := match valueRaw with
            | .str "true" => true
            | .str "false" => false
            | _ => none
            match value? with
            | .some value => do
              bools := bools.push (e, value)
            | none => pure ()
          | "Int" =>
            let value? : Option Int := match valueRaw with
            | .const n => some n
            | .list [.str "-", .const n] => some (-n)
            | _ => none
            match value? with
            | .some value => do
              ints := ints.push (e, value)
            | none => pure ()
          | _ => pure ()
        | none => pure ()
      | _ => pure ()
  | _ => return .unknown
  return .model (makeSmtModel ints.toList bools.toList)

def smtHeader := "(set-option :produce-models true)
(set-logic NIA)
(define-fun nat-sub ((a Int) (b Int)) Int (ite (< a b) 0 (- a b)))
"

def runSolver (lines : Array SmtExpr) : Lean.Elab.Tactic.TacticM SolverOutputRaw
:= do
  let child ← IO.Process.spawn {
    cmd := "z3", args := #["-T:2", "-in"],
    -- cmd := "cvc5", args := #["--tlimit=2000", "-"],
    -- cmd := "cvc4", args := #["--tlimit=2000", "--lang=smtlib", "-"],
    stdin := .piped,
    stdout := .piped,
    stderr := .null
  }
  child.stdin.putStr smtHeader
  for line in lines do
    child.stdin.putStr line.toString
    child.stdin.putStr "\n"
  child.stdin.putStr "(check-sat)\n"
  child.stdin.flush
  let result ← child.stdout.getLine
  if result == "sat\n" then
    child.stdin.putStr "(get-model)\n"
    let modelStr ← child.stdout.readToEnd
    match smtParser.singleton modelStr with
    | some modelRaw => return .model modelRaw
    | none => return .unknown
  else if result == "unsat\n" then
    return .unsat
  else
    return .unknown

def SolverOutput.log : SolverOutput → Lean.Meta.MetaM Unit
| .unsat => Lean.logInfo "Unsatisfiable"
| .unknown => Lean.logInfo "Unknown"
| .model m => do
  Lean.logInfo (← m.toString)

private axiom intHammerSorry.{u} (α : Sort u) : α

macro "int_hammer_sorry" : tactic =>
  `(tactic | exact @intHammerSorry _)

def intHammer : Lean.Elab.Tactic.TacticM Unit := do
  let (smtLines, ctx) ← stateToSmt
  let solverOutputRaw : SolverOutputRaw ← runSolver smtLines
  let solverOutput : SolverOutput
    := StateT.run' (solverOutputRaw.toLean) ctx
  match solverOutput with
  | .unsat =>
    Lean.Elab.Tactic.evalTactic <| ← `(tactic | int_hammer_sorry)
  | _ => Lean.Elab.Tactic.withMainContext do
    solverOutput.log

elab "int_hammer" : tactic => do
  intHammer

#check String.intercalate

elab "int_hammer_show_smt" : tactic => do
  let (smtLines, ctx) ← stateToSmt
  Lean.logInfo (smtHeader ++ (String.intercalate "\n" (
    smtLines.toList.map SmtExpr.toString
  )))

#check Lean.Expr

example (a b : Int) : a = 3 → a^3 = 27 := by
  int_hammer
