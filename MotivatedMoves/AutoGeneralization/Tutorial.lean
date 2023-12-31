import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/
import MotivatedMoves.AutoGeneralization.mulPermuteProof

open Lean Elab Tactic Meta Term

#eval Lean.versionString -- 4.3.0-rc1

/-- Tactic that does nothing. -/
elab "doNothing" : tactic => do
  return

example : True := by
  doNothing
  trivial

/-- Tactic that prints the goal -/
elab "printGoal" : tactic => do
  let goal ← getMainGoal
  logInfo goal

example : True := by
  printGoal -- True
  trivial

theorem reflExample : 0 = 0 := by
  rfl
#print reflExample

example : 1+1=2 := by
  printGoal -- 1+1=2
  trivial

/-- Tactic that still prints the goal-/
elab "printGoalType" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  logInfo goalType

example : True := by
  printGoalType -- True
  trivial

example : 1+1=2 := by
  printGoalType -- 1+1=2
  trivial

/-- Tactic that prints the type of the type of the goal (e.g. Prop) --/
elab "printGoalTypeType" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let goalTypeType ← inferType goalType
  logInfo goalTypeType

example : True := by
  printGoalTypeType -- Prop
  trivial

example : 1+1=2 := by
  printGoalTypeType -- Prop
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
elab "mySorry" : tactic => do
  let goal ← getMainGoal
  admitGoal goal

/-- A sorry macro -/
macro "mySorry" : tactic =>
  `(tactic| sorry)

/--  Tactic that takes a hypothesis as an argument -/
macro "contraposWith" h:ident : tactic => `(tactic|
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
  contraposWith p
  simp

/-- Tactic that takes two tactics as arguments -/
macro "andThen" a:tactic b:tactic : tactic => `(tactic|
  ($a:tactic; all_goals $b:tactic))

/-- Without and_then -/
example: 1=1 ∧ 2=2 := by
  constructor -- split into two goals:  1 = 1 and 2 = 2
  rfl; rfl  -- solve each one

/-- With and_then -/
example: 1=1 ∧ 2=2 := by
  andThen constructor rfl

/--  More intuitive syntax for the above tactic  -/
syntax tactic " andThen " tactic : tactic
macro_rules
| `(tactic| $a:tactic andThen $b:tactic) =>
    `(tactic| andThen $a $b)

example: 1 = 1 ∧ 2 = 2 := by
  constructor andThen rfl

/--  Tactic to print all non-implementation-detail hypotheses -/
def printHypotheses : MetaM Unit :=
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hypName := ldecl.userName
    let hypType := ldecl.type
    let hypExpr := ldecl.toExpr
    -- logInfo m!"Name: '{hypName}'  Type: '{hypType}'"
    logInfo m!"Name: '{hypName}'  Type: '{hypType}'   Expr: '{hypExpr}'"

def printAllHypotheses : TacticM Unit := do
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    let hypName := ldecl.userName
    let hypType := ldecl.type
    let hypExpr := ldecl.toExpr
    -- logInfo m!"Name: '{hypName}'  Type: '{hypType}'"
    logInfo m!"Name: '{hypName}'  Type: '{hypType}'   Expr: '{hypExpr}'"


elab "printAllHypotheses" : tactic => do
  printAllHypotheses

theorem testPrintHyp {P Q : Prop} (p : P) (q: Q): P := by
  printAllHypotheses
  assumption
```
/--  Tactic to return hypotheses declarations-/
def getHypotheses : MetaM (List LocalDecl) := do
  let mut hypotheses : List LocalDecl := []
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses

/--  Tactic to return hypotheses declarations (including dynamically generated ones)-/
def getAllHypotheses : TacticM (List LocalDecl) := do
  let mut hypotheses : List LocalDecl := []
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses

/--  Tactic to return hypotheses expressions (the types)-/
def getHypothesesTypes : MetaM (List Expr) := do
  let mut hypotheses_types : List Expr := []
  for hypothesis in ← getHypotheses do
    hypotheses_types := hypothesis.type :: hypotheses_types
  return hypotheses_types

def getAllHypothesesTypes : TacticM (List Expr) := do
  let mut hypotheses_types : List Expr := []
  for hypothesis in ← getAllHypotheses do
    hypotheses_types := hypothesis.type :: hypotheses_types
  return hypotheses_types

/--  Tactic to return hypotheses names-/
def getHypothesesNames : MetaM (List Name) := do
  let mut hypotheses_names : List Name := []
  for hypothesis in ← getHypotheses do
    hypotheses_names := hypothesis.userName :: hypotheses_names
  return hypotheses_names
elab "getHypothesesNames" : tactic => do
  let names ← getHypothesesNames
  logInfo ("Hyp names:" ++ toString names)

def getAllHypothesesNames : TacticM (List Name) := do
  let mut hypotheses_names : List Name := []
  for hypothesis in ← getAllHypotheses do
    hypotheses_names := hypothesis.userName :: hypotheses_names
  return hypotheses_names
elab "getAllHypothesesNames" : tactic => do
  let names ← getAllHypothesesNames
  logInfo ("Hyp names:" ++ toString names)



example {P Q : Prop} (p : P) (q: Q): P := by
  getHypothesesNames
  assumption

/--  Tactic get a hypothesis by its name -/
def getHypothesisByName (h : Name) : TacticM LocalDecl := do
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    if ldecl.userName == h then
      return ldecl
  throwError "No hypothesis by that name."

/-- Get the proposition for a given hypothesis (given its name) -/
def getHypothesisType (h : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName h
  return hyp.type

/-- Get the proof of a given hypothesis (given its name) -/
def getHypothesisProof (h : Name) : TacticM Expr := do
  let hyp ← getHypothesisByName h
  if hyp.hasValue
    -- then return hyp.value
    then
      let val ← getExprMVarAssignment? hyp.value.mvarId!
      return ← val
    else throwError "The hypothesis was likely declared with a 'have' rather than 'let' statement, so its proof is not accessible."


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
  let goalDecl ← getGoalDecl
  for hypDecl in ← getHypotheses do
    if ← isDefEq hypDecl.type goalDecl.type then
      closeMainGoal hypDecl.toExpr

example {P : Prop} (p : P): P := by
  assump -- works

example {P : Prop} : P := by
  assump -- does nothing
  sorry

/-- Demonstrate the difference between dbg_trace and logInfo -/
elab "printMessages" : tactic =>
  dbg_trace "The dbg_trace message"
  logInfo "The logInfo message"

example : True := by
  printMessages
  simp

/--  Tactic that closes goal with a matching hypothesis if available, throws error if not-/
elab "assump'" : tactic => do
  let goalDecl ← getGoalDecl

  -- check if any of the hypotheses matches the goal.
  for hypDecl in ← getHypotheses do
    if ← isDefEq hypDecl.type goalDecl.type then
      closeMainGoal hypDecl.toExpr
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
  let goalDecl ← getGoalDecl
  let hypDecls ← getHypotheses

  -- check if any of the hypotheses matches the goal.
  let matchingHypDecl ← hypDecls.findM? (
    -- when isDefEq returns true, we return the corresponding hypDecl
    -- if it never does, we return none
    fun hypDecl => return ← isDefEq hypDecl.type goalDecl.type
  )

   -- close the goal, or fail if no hypothesis matched
  match matchingHypDecl with
  | some hypDecl => closeMainGoal hypDecl.toExpr
  | none => throwError "No matching assumptions."

theorem testAssumpSuccess {P : Prop} (p : P): P := by
  assump''

theorem testAssumpFails {P Q : Prop} (p : P): Q := by
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
| m, n =>  Expr.app (.app (.const `Nat.add []) (natExpr m)) (natExpr n)
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

theorem reflOfZero : 0=0:= by
  print_goal_as_expression
  simp

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

/-- What the expression looks like, but prettier  --/
def logDelabExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{← Lean.PrettyPrinter.delab e}"

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
#eval logDelabExpression zero    -- `Nat.zero
#eval logExpressionType zero    -- Nat
-- #eval logCompiledExpression zero -- 0

/-- Getting theorems from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.type -- return the theorem statement (the type is the proposition)

#eval do {let e ← getTheoremStatement `multPermute; logExpression e}

#eval getTheoremStatement `multPermute
#eval do {let e ← getTheoremStatement `multPermute; logPrettyExpression e}

#eval do {let e ← getTheoremStatement `multPermute; logFormattedExpression e}
#eval do {let e ← getTheoremStatement `multPermute; logExpressionType e}

/-- Getting theorem proof from context --/
def getTheoremProof (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.value! -- return the theorem proof (the term is the proof)

#eval do {let e ← getTheoremProof `reflOfZero; logExpression e}
#eval do {let e ← getTheoremProof `reflOfZero; logFormattedExpression e}
#eval do {let e ← getTheoremProof `reflOfZero; logPrettyExpression e}


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

/- (For debugging) Print what type of expression something is -/
def printExprType (e : Expr) : MetaM Unit := do
  logInfo e.ctorName

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
    | Expr.mvar m            => return [e] ++ acc
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

def isAtomicNat (e : Expr) : MetaM Bool := do
  if not (← isNat e) then return false
  else
    let rec getFirstNonAppTerm (e : Expr) : MetaM Expr := match e with
    | Expr.app f a => return (← getFirstNonAppTerm f)
    | _ => return e
    let nonAppTerm ← getFirstNonAppTerm e
    -- dbg_trace repr e
    -- dbg_trace ">>>"
    if nonAppTerm.isConstOf `OfNat.ofNat --nonAppTerm.isLit -
      then
        -- dbg_trace repr nonAppTerm; dbg_trace "==========";
        return true
      else
        -- dbg_trace repr nonAppTerm; dbg_trace "==========";
        return false

#eval toExpr 1
#eval sumExpr 1 2
#eval isAtomicNat (toExpr 1) -- true
#eval isAtomicNat (sumExpr 1 2) -- false

/- Get (in a list) all subexpressions that are just a single natural numbers -/
def getIfAtomicNat (subexpr : Expr) : MetaM (Option Expr) := do
  if (← isAtomicNat subexpr)
    then return some subexpr
    else return none

/-- Returns single nats like 3 and 4, not 3^4 or 3*4 -/
def getAtomicNatsIn (e : Expr) : MetaM (List Expr) := do
  let subexprs ← getSubexpressionsIn e
  let natSubexprs ← subexprs.filterMapM getIfAtomicNat
  return natSubexprs

#eval do { let e ← getTheoremStatement `flt_example; let natsInE ← getNatsIn e; natsInE.forM logPrettyExpression}
#eval do { let e ← getTheoremStatement `flt_example; let natsInE ← getAtomicNatsIn e; natsInE.forM logPrettyExpression}

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
  createReflexivityGoal; swap
  simp; simp

elab "createReflexivityGoal'" : tactic => do
  let goalType ← mkEq (Expr.const ``Nat.zero []) (Expr.const ``Nat.zero [])
  createGoal goalType
example : 1 + 2 = 3 := by
  createReflexivityGoal'
  simp; simp

/-- Introduce a hypothesis already in the goal -/
elab "introductor" : tactic => do
  let goal ← getGoalVar
  let (_, new_goal) ← goal.intro `h
  setGoals [new_goal]

elab "introductor'" : tactic => do
  liftMetaTactic fun goal => do
    let (_, new_goal) ← goal.intro `wow
    return [new_goal]

example (P Q : Prop) : P → Q → P := by
  introductor
  introductor
  assumption

/-- Create a new hypothesis -/

def createHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  let hyp : Hypothesis := { userName := hypName, type := hypType, value := hypProof }
  let (_, new_goal) ← (←getGoalVar).assertHypotheses (List.toArray [hyp])
  setGoals [new_goal]

elab "createNatHypothesis" : tactic => do
  let hypType := Expr.const ``Nat []
  let hypProof :=  (toExpr 0) -- use 0 as a term of type Nat
  createHypothesis hypType hypProof `x

example : 1 + 2 = 3 := by
  createNatHypothesis
  simp

elab "createReflHypothesis" : tactic => do
  let hypType ← mkEq (toExpr 0) (toExpr 0) -- make the metavariable goal to prove that "0 = 0"
  let hypProof := Lean.mkAppN (.const ``Eq []) #[(toExpr 0), (toExpr 0)] -- proof that Eq 0 0
  createHypothesis hypType hypProof

example : 1 + 2 = 3 := by
  createReflHypothesis
  simp

/-- Helper for incrementing idx when creating pretty names-/
partial def mkPrettyNameHelper(hypNames : List Name) (base : Name) (i : Nat) : Name :=
  let candidate := base.appendIndexAfter i
  if (hypNames).contains candidate then
    mkPrettyNameHelper hypNames base (i+1)
  else
    candidate

/-- Names a function baseName_idx if that is available.  otherwise, names it baseName_idx+1 if available...and so on. -/
def mkPrettyName (baseName : Name) (idx : Nat) : TacticM Name := do
  return mkPrettyNameHelper (← getAllHypothesesNames) baseName idx

/-- Generalizing a term in a theorem  -/
def generalizeTerm (e : Expr) (x? : Option Name := none) (h? : Option Name := none) : TacticM Unit := do
    let x := x?.getD (← mkPrettyName `x 0) -- use the given variable name, or if it's not there, make one
    let h := h?.getD (← mkPrettyName `h 0) -- use the given hypothesis name, or if it's not there, make one
    let genArg : GeneralizeArg := { expr := e, xName? := x, hName? := h }
    let (_, new_goal) ← (←getGoalVar).generalize (List.toArray [genArg])
    setGoals [new_goal]

    -- TODO return the type of the generalized term..

elab "generalize2" : tactic => do
  let e := (toExpr 2)
  let x := `x
  let h := `h
  generalizeTerm e -- like the lean command "generalize h : e = x"

elab "generalize4" : tactic => do
  let e := (toExpr 4)
  let x := `x
  let h := `h
  generalizeTerm e  -- like the lean command "generalize h : e = x"

example : 2^4 % 5 = 1 := by
  generalize2
  generalize4
  rw [← h_0, ← h_1]; rfl

/-- Generalizing all natural numbers in a theorem  -/
elab "generalizeAllNats" : tactic => do
  let nats ← getAtomicNatsIn (← getGoalType)
  nats.forM generalizeTerm

example : 2^4 % 5 = 1 := by
  generalizeAllNats
  rw  [←h_0, ←h_1, ←h_2, ←h_3]; rfl

def syntaxToExpr (e : TermElabM Syntax) : TermElabM Unit := do
  let e ← elabTermAndSynthesize (← e) none
  logExpression e

#eval syntaxToExpr `(@HMul.hMul Nat Nat Nat instHMul)

elab "generalizef" : tactic => do
  let hmul := .const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]
  let nat := .const ``Nat []
  let inst :=   mkApp2 (.const `instHMul [Lean.Level.zero]) nat (.const `instMulNat [])
  let f := mkApp4 hmul nat nat nat inst
  generalizeTerm f

example : True := by
  generalizef
  simp

/-- Gets all identifier names in an expression -/
def getFreeIdentifiers (e : Expr) : List Name := e.getUsedConstants.toList

-- Demonstration of using the replace function
def originalExpr : Expr := mkApp2 (Expr.const `Nat.add []) (mkNatLit 1) (mkNatLit 1)
def replacementFunction : Expr → Option Expr
  | .lit (Literal.natVal 1) => some $ .lit (Literal.natVal 2)
  | _                      => none
def replacedExpr : Expr := originalExpr.replace replacementFunction
#eval ppExpr originalExpr
#eval ppExpr replacedExpr

/-- Creating a replacementRule to replace a -/
def replacementRule : Expr → Option Expr
  | .lit (Literal.natVal 1) => some $ .lit (Literal.natVal 2)
  | _                      => none

/-- Generalizing all natural numbers in a theorem  -/
def autogeneralize (hypName : Name) : TacticM Unit := do
  -- Print the proof
  let hypType ← getHypothesisType hypName
  let hypProof ← getHypothesisProof hypName

  -- generalize the term "f"
  let hmul := .const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]
  let nat := .const ``Nat []
  let inst :=   mkApp2 (.const `instHMul [Lean.Level.zero]) nat (.const `instMulNat [])
  let f := mkApp4 hmul nat nat nat inst
  generalizeTerm f

  -- know that the type of the generalized term is N -> N -> N
  let t ← `(ℕ → ℕ → ℕ)

  -- get all free identifiers (that is, constants) in the proof term that don't already appear in the proof type
  let freeIdentsInProofType := getFreeIdentifiers hypType
  let freeIdentsInProofTerm := getFreeIdentifiers hypProof
  let freeIdents := freeIdentsInProofTerm.removeAll freeIdentsInProofType
  logInfo (toString freeIdents)

  -- now get the types of those identifiers
  let freeIdentsTypes ← liftMetaM (freeIdents.mapM getTheoremStatement)

  -- only keep the ones that contain the generalized term (multiplication *) in their type
  let freeIdentsContainingF := freeIdentsTypes.filter f.occurs
  logInfo freeIdentsContainingF

elab "autogeneralize" h:ident : tactic =>
  autogeneralize h.getId

example : True := by
  let multPermuteHyp :  ∀ (n m p : ℕ), n * (m * p) = m * (n * p) := by {intros n m p; rw [← Nat.mul_assoc]; rw [@Nat.mul_comm n m]; rw [Nat.mul_assoc]}
  autogeneralize multPermuteHyp -- adds multPermuteGen to list of hypotheses
  simp [multPermuteHyp] -- to make sure the linter doesn't complain that multPermute wasn't used in proving "True"
