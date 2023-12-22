import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/

open Lean Elab Tactic Meta

#eval Lean.versionString -- 4.3.0-rc1

/-- Tactic that does nothing. -/
elab "do_nothing" : tactic => do
  return

example : True := by
  do_nothing
  trivial

/-- Tactic that prints the goal -/
elab "print_goal" : tactic => do
  let goal ← getMainGoal
  logInfo goal

example : True := by
  print_goal -- True
  trivial

example : 1+1=2 := by
  print_goal -- 1+1=2
  trivial

/-- Tactic that still prints the goal-/
elab "print_goal_type" : tactic => do
  let goal ← getMainGoal
  let goal_type ← goal.getType
  logInfo goal_type

example : True := by
  print_goal_type -- True
  trivial

example : 1+1=2 := by
  print_goal_type -- 1+1=2
  trivial

/-- Tactic that prints the type of the type of the goal (e.g. Prop) --/
elab "print_goal_type_type" : tactic => do
  let goal ← getMainGoal
  let goal_type ← goal.getType
  let goal_type_type ← inferType goal_type
  logInfo goal_type_type

example : True := by
  print_goal_type_type -- Prop
  trivial

example : 1+1=2 := by
  print_goal_type_type -- Prop
  trivial

/-- Prove that taking the contrapositive is logically valid --/
theorem ctrp {P Q : Prop} : (¬ Q → ¬ P) → (P → Q) := by
  intros h p; by_contra nq; apply h nq p

example {P : Prop} : P → True := by
  apply ctrp
  simp


-- elab "contrap" : tactic => do
--   apply ctrp -- THROWS ERROR

/-- Change the proof state with contrapositive -/
macro "contrapos" : tactic =>
  `(tactic| apply ctrp)

example : P → True := by
  contrapos
  simp

/-- A sorry elab -/
elab "my_sorry" : tactic => do
  let goal ← getMainGoal
  admitGoal goal

/-- A sorry macro -/
macro "my_sorry" : tactic =>
  `(tactic| sorry)

/--  Tactic that takes a hypothesis as an argument -/
macro "contrapos_with" h:ident : tactic => `(tactic|
  (revert $h; contrapose)
)

example {P Q : Prop} :  P → Q → True  := by
  intro p
  contrapose
  simp

example {P Q : Prop} :  P → Q → True  := by
  intro p q
  revert p
  contrapose
  simp

example {P Q : Prop} :  P → Q → True  := by
  intro p q
  contrapos_with p
  simp

/-- Tactic that takes two tactics as arguments -/
macro "and_then" a:tactic b:tactic : tactic => `(tactic|
  ($a:tactic; all_goals $b:tactic))

/-- Without and_then -/
example: 1=1 ∧ 2=2 := by
  constructor -- split into two goals:  1 = 1 and 2 = 2
  rfl; rfl  -- solve each one

/-- With and_then -/
example: 1=1 ∧ 2=2 := by
  and_then constructor rfl

/--  More intuitive syntax for the above tactic  -/
syntax tactic " and_then " tactic : tactic
macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| and_then $a $b)

example: 1 = 1 ∧ 2 = 2 := by
  constructor and_then rfl

/--  Tactic to print all non-implementation-detail hypotheses -/
def print_hypotheses : MetaM Unit :=
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hyp_name := ldecl.userName
    let hyp_type := ldecl.type
    -- let hyp_expr := ldecl.toExpr
    logInfo m!"Name: '{hyp_name}'  Type: '{hyp_type}'"
    -- logInfo m!"Name: '{hyp_name}'  Type: '{hyp_type}'   Expr: '{hyp_expr}'"

elab "print_hypotheses" : tactic => do
  print_hypotheses

theorem test_print_hyp {P Q : Prop} (p : P) (q: Q): P := by
  print_hypotheses
  assumption

/--  Tactic to return hypotheses declarations-/
def getHypotheses : MetaM (List LocalDecl) := do
  let mut hypotheses : List LocalDecl := []
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses

/--  Tactic to return hypotheses expressions (the types)-/
def getHypothesesTypes : MetaM (List Expr) := do
  let mut hypotheses_types : List Expr := []
  for hypothesis in ← getHypotheses do
    hypotheses_types := hypothesis.type :: hypotheses_types
  return hypotheses_types

/--  Tactic to return goal variable -/
def getGoalVar : TacticM MVarId := do
  return ← getMainGoal

/--  Tactic to return goal declaration-/
def getGoalDecl : TacticM MetavarDecl := do
  return ← getMainDecl -- (← getGoalVar).getDecl

/--  Tactic to return goal expression (the type) -/
def getGoalType : TacticM Expr := do
  return ← getMainTarget -- (← getGoalDecl).type or (← getGoalVar).getType

/--  Tactic to experiment with MetaM vs TacticM -/
def lookIntoEnvironment  : MetaM Unit := do
  let env ← getEnv
  dbg_trace (env.contains `multPermute)

#eval lookIntoEnvironment

/--  Tactic that closes goal with a matching hypothesis if available-/
elab "assump" : tactic => do
  let goal_decl ← getGoalDecl
  for hyp_decl in ← getHypotheses do
    if ← isDefEq hyp_decl.type goal_decl.type then
      closeMainGoal hyp_decl.toExpr

example {P : Prop} (p : P): P := by
  assump -- works

example {P : Prop} : P := by
  assump -- does nothing
  sorry

/--  Tactic that closes goal with a matching hypothesis if available, throws error if not-/
elab "assump'" : tactic => do
  let goal_decl ← getGoalDecl

  -- check if any of the hypotheses matches the goal.
  for hyp_decl in ← getHypotheses do
    if ← isDefEq hyp_decl.type goal_decl.type then
      closeMainGoal hyp_decl.toExpr
      return

  -- if no hypothesis matched, this tactic fails.
  throwError "No matching assumptions."

example {P : Prop} (p : P): P := by
  assump' -- works

example {P : Prop} : P := by
  assump' -- throws error "No matching assumptions."
  sorry

/--  Tactic that behaves identically to the above, but takes advantage of built-in looping with findM -/
elab "assump''" : tactic => do
  let goal_decl ← getGoalDecl
  let hyp_decls ← getHypotheses

  -- check if any of the hypotheses matches the goal.
  let matching_hyp_decl ← hyp_decls.findM? (
    -- when isDefEq returns true, we return the corresponding hyp_decl
    -- if it never does, we return none
    fun hyp_decl => return ← isDefEq hyp_decl.type goal_decl.type
  )

   -- close the goal, or fail if no hypothesis matched
  match matching_hyp_decl with
  | some hyp_decl => closeMainGoal hyp_decl.toExpr
  | none => throwError "No matching assumptions."

theorem test_assump_success {P : Prop} (p : P): P := by
  assump''

theorem test_assump_fails {P Q : Prop} (p : P): Q := by
  assump''
  sorry

/-- Create 0, 1, and π -/
def zero := Expr.const ``Nat.zero []
#eval zero

def one := Expr.app (.const ``Nat.succ []) zero
#eval one

def two := Expr.app (.const ``Nat.succ []) one
#eval two

#check Real.pi
def pi := Expr.const ``Real.pi []
#eval pi

/-- Elaborate it -/
-- elab "zero" : term => return zero
-- #eval zero -- 0

elab "one" : term => return one
#eval one -- 1

/-- Turn lean Nats into Expressions -/
def natExpr: Nat → Expr
| 0 => .const ``Nat.zero []
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)
#eval natExpr 2

#check Nat.add

def sumExpr: Nat → Nat → Expr
| m, n =>  natExpr (m+n)
#eval sumExpr 1 2

-- Check if you got the right answer by making sure the below line evaluates to "true"
#eval isDefEq (sumExpr 1 2) (Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero []))))

/- Turn Lean Expressions back into Nats with evalExpr -/
def expectedType := Expr.const ``Nat []
def value := (sumExpr 1 2)
#eval evalExpr Nat expectedType value

/- Turn Lean Expressions back into Nats with elab -/
elab "sumExpr12" : term => return (sumExpr 1 2)
#eval sumExpr12

/- Get types of Lean constant expressions -/
#eval zero.isConst  -- true, is a natural number constant
#eval pi.isConst    -- true, is a real number constant

#eval inferType zero  -- Lean.Expr.const `Nat []
#eval inferType pi    -- Lean.Expr.const `Real []

#eval (Expr.const `Nat []).isConstOf `Nat -- true
#eval (Expr.const `Nat []).isConstOf `Real -- false

def isNat (e: Expr): MetaM Bool := do
  let type_expr ← inferType e
  return type_expr.isConstOf `Nat

#eval isNat zero
#eval isNat pi


/- Get types of Lean constant expressions, with debugging -/
def isNatDebug (e: Expr): MetaM Unit := do
  let type_expr ← inferType e
  dbg_trace "The type expression is: {type_expr}"

#eval isNatDebug zero

def isNatDebugRepr (e: Expr): MetaM Unit := do
  let type_expr ← inferType e
  dbg_trace "The type expression is: {repr type_expr}"

#eval isNatDebugRepr zero

def sayHello : MetaM Unit := do
  logInfo "hi"

#eval sayHello

elab "sayHello" : tactic => sayHello

example : True := by
  sayHello
  trivial

/- Applications -/
def f := Expr.const `Nat.succ []
def x := Expr.const `Nat.zero []
#eval (Expr.app f x) -- Nat.succ Nat.zero

elab "fx" : term => return (Expr.app f x)
#eval (fx = Nat.succ Nat.zero) -- true

def f' := Expr.const `Nat.add []
def x' := Expr.const `Nat.zero []
def y' := Expr.const `Nat.zero []
#eval (Expr.app (.app f' x') y') -- Nat.add Nat.zero Nat.zero

elab "fxy" : term => return (Expr.app (.app f' x') y')
#eval (fxy = Nat.add Nat.zero Nat.zero) -- true

/- Applications puzzle -/
def addExpr := Expr.const `Nat.add []
def mulExpr := Expr.const `Nat.mul []

def sumExpr': Nat → Nat → Expr
| m, n =>  (Expr.app (.app addExpr (natExpr m)) (natExpr n))
def mulExpr': Nat → Nat → Expr
| m, n =>  (Expr.app (.app mulExpr (natExpr m)) (natExpr n))

elab "sum12" : term => return sumExpr' 1 2
elab "mul12" : term => return mulExpr' 1 2
#eval (sum12 = 3) -- should be true
#eval (mul12 = 2) -- should be true

/- Get types of Lean application expressions -/
#eval (sumExpr 1 2).isConst -- false, is an application
#eval (sumExpr 1 2).isApp   -- true, is an application

def isAddition (e : Expr) :  MetaM Bool := do
  -- dbg_trace "The function: {e.getAppFn}"
  if (← isDefEq e.getAppFn addExpr) then return true else return false

#eval isAddition (sumExpr' 1 2) -- true
#eval isAddition (mulExpr' 1 2) -- false

/-- Given the compiled code in the goal, _print_ the full raw format of an expression  --/
elab "print_goal_as_expression" : tactic => do
  let goal ← getGoalType
  logInfo (toExpr goal) -- or logInfo (repr goalt)

example :1+1=2 := by
  print_goal_as_expression
  ring

example :0=0 := by
  print_goal_as_expression
  ring

theorem multPermute : ∀ (n m p : Nat), n * (m * p) = m * (n * p) := by
  print_goal_as_expression
  ring; simp

/-- What the expression looks like --/
def logExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{repr e}"
#eval logExpression zero

/-- What the expression looks like, but prettier  --/
def logFormattedExpression (e : Expr) : MetaM Unit := do
  let s := Format.pretty (format e)
  dbg_trace "{s}"

/-- What the expression looks like, but prettier  --/
def logPrettyExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{←ppExpr e}"

/-- What type the expression compiles to  --/
def logExpressionType (e : Expr) : MetaM Unit :=
  do
    let t ← inferType e
    dbg_trace t

-- def logCompiledExpression (e : Expr) : MetaM Unit := do
--   dbg_trace "{e}"
#eval logExpression zero        -- Lean.Expr.const `Nat.zero []
#eval logFormattedExpression zero    -- Nat.zero
#eval logPrettyExpression zero    -- Nat.zero
#eval logExpressionType zero    -- Nat
-- #eval logCompiledExpression zero -- 0

/-- Getting theorems from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.type -- return the theorem statement

#eval do {let e ← getTheoremStatement `multPermute; logExpression e}

#eval getTheoremStatement `multPermute
#eval do {let e ← getTheoremStatement `multPermute; logPrettyExpression e}

#eval do {let e ← getTheoremStatement `multPermute; logFormattedExpression e}
#eval do {let e ← getTheoremStatement `multPermute; logExpressionType e}

/-- Print all subexpressions that involve constants --/
def printConstantsIn (e : Expr) : MetaM Unit :=
  e.forEachWhere Expr.isConst logExpression

#eval do {let e ← getTheoremStatement `multPermute; printConstantsIn e}

/-- Print all subexpressions that involve natural numbers --/
def printIfNat (subexpr : Expr) : MetaM Unit := do
  try
    let isNatResult ← isNat subexpr
    if isNatResult
      then logPrettyExpression subexpr; dbg_trace "---"
      else return
  catch
  | Exception.error _ _ => return
  | _ => throwError "Something about 'isNat subexpr' is throwing an error."

def printNatsIn (e : Expr) : MetaM Unit := do
  e.forEach printIfNat

#eval do {let e ← getTheoremStatement `multPermute;  printNatsIn e}

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

#eval do {let e ← getTheoremStatement `multPermute;  getSubexpressionsIn e}

/- Get (in a list) all subexpressions that involve natural numbers -/
def getIfNat (subexpr : Expr) : MetaM (Option Expr) := do
  try
    let isNatResult ← isNat subexpr
    if isNatResult
      then return some subexpr
      else return none
  catch
  | Exception.error _ _ => return none
  | _ => throwError "Something about 'isNat subexpr' is throwing an error."


def getNatsIn (e : Expr) : MetaM (List Expr) := do
  let subexprs ← getSubexpressionsIn e
  let natSubexprs ← subexprs.filterMapM getIfNat
  return natSubexprs

theorem flt_example : 2^4 % 5 = 1 := by simp

#eval do { let e ← getTheoremStatement `flt_example; let natsInE ← getNatsIn e; natsInE.forM logPrettyExpression}
#eval do { let e ← getTheoremStatement `multPermute; let natsInE ← getNatsIn e; natsInE.forM logPrettyExpression}

/-- Create new goals -/
def createGoal (goalType : Expr) : TacticM Unit := do
  let goal ← mkFreshExprMVar goalType
  appendGoals [goal.mvarId!]

elab "createNatGoal" : tactic => do
  let goalType := (Expr.const ``Nat []) -- make the goal to find an instance of type "Nat"
  createGoal goalType

example : 1 + 2 = 3 := by
  createNatGoal
  simp; use 5

elab "createReflexivityGoal" : tactic => do
  let goalType ← mkEq (toExpr 0) (toExpr 0) -- make the metavariable goal to prove that "0 = 0"
  createGoal goalType

example : 1 + 2 = 3 := by
  createReflexivityGoal
  simp; simp

elab "createReflexivityGoal'" : tactic => do
  let goalType ← mkEq (Expr.const ``Nat.zero []) (Expr.const ``Nat.zero [])
  createGoal goalType

example : 1 + 2 = 3 := by
  createReflexivityGoal'
  simp; simp
