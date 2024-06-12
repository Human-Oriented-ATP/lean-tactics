import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/
import Mathlib.Data.Real.Irrational

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize

/-- Getting theorems from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | throwError ("Could not find a theorem with name " ++ n) -- get the declaration with that name
  return thm.type -- return the theorem statement (the type is the proposition)

/--  Tactic to return hypotheses declarations (including dynamically generated ones)-/
def getHypotheses : TacticM (List LocalDecl) := do
  let mut hypotheses : List LocalDecl := []
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses

/--  Tactic to return hypotheses names-/
def getHypothesesNames : TacticM (List Name) := do
    return (← getHypotheses).map (fun hypothesis => hypothesis.userName)

/--  Tactic get a hypothesis by its name -/
def getHypothesisByName (h : Name) : TacticM LocalDecl := do
  let goal ← getMainGoal  -- the dynamically generated hypotheses are associated with this particular goal
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then continue
    if ldecl.userName == h then
      return ldecl
  throwError m!"No hypothesis by name '{h}'."

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
          else
            return hyp.value -- works if proved directly with a proof term like `:= fun ...`
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

/-- Create new goals -/
def createGoal (goalType : Expr) : TacticM Unit := do
  let goal ← mkFreshExprMVar goalType
  appendGoals [goal.mvarId!]

/-- Create a new hypothesis using a "have" statement -/
def createHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  let hyp : Hypothesis := { userName := hypName, type := hypType, value := hypProof }
  let (_, new_goal) ← (←getGoalVar).assertHypotheses (List.toArray [hyp])
  setGoals [new_goal]

/-- Create a new hypothesis using a "let" statement (so its proof is accessible)-/
def createLetHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  -- (←getGoalVar).withContext do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  let new_goal ← (←getGoalVar).define hypName hypType hypProof
  let (_, new_goal) ← intro1Core new_goal true
  setGoals [new_goal]



/-- Print out an expression in a human-readable way  --/
def printPrettyExpression (e : Expr) : MetaM Unit := do
  dbg_trace "{←ppExpr e}"

/-- Turn syntax into fully elaborated expressions --/
def syntaxToExpr (e : TermElabM Syntax) : TermElabM Expr := do
  let e ← elabTermAndSynthesize (← e) none
  return e
#eval syntaxToExpr `(2+3=5)

/-- Turn code into fully elaborated expressions --/
elab "#term_to_expr" t:term : command => do
  let e ← liftTermElabM (Term.elabTerm t none)
  logInfo m!"The expression corresponding to {t} is:\n\n{repr e}"
#term_to_expr (2+3=5)
#term_to_expr (Eq.refl 0)



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

/- Get (in a list) all subexpressions in an expression -/
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
  let subexprs := subexprs.filter $ fun subexpr => !subexpr.hasLooseBVars -- remove the ones that will cause errors when parsing
  subexprs

/-- Helper for incrementing idx when creating pretty names-/
partial def mkPrettyNameHelper(hypNames : List Name) (base : Name) (i : Nat) : Name :=
  let candidate := base.appendIndexAfter i
  if (hypNames).contains candidate then
    mkPrettyNameHelper hypNames base (i+1)
  else
    candidate

/-- Names a function baseName_idx if that is available.  otherwise, names it baseName_idx+1 if available...and so on. -/
def mkPrettyName (baseName : Name) (idx : Nat) : TacticM Name := do
  return mkPrettyNameHelper (← getHypothesesNames) baseName idx

/-- Gets all identifier names in an expression -/
def getFreeIdentifiers (e : Expr) : List Name := e.getUsedConstants.toList

/-- Create the expression d → b with name n-/
def mkImplies (n : Name := `h) (d b : Expr) : MetaM Expr :=
  return .forallE (← mkFreshUserName n) d b .default

/-- Create a reasonable name for an expression -/
def mkAbstractedName (n : Name) : Name :=
    match n with
    | (.str _ s) => s!"f_{s.takeWhile (fun c => c != '_')}" -- (fun c => c.isLower && c != '_')
    | _ => `unknown

#eval mkAbstractedName `prime_two
#eval mkAbstractedName `instAddCommSemigroupInt

/-- Returns true if "e" contains "subexpr".  Differs from "occurs" because this uses the coarser "isDefEq" rather than "==" -/
def containsExpr(subexpr : Expr)  (e : Expr) : MetaM Bool := do
  let mctx ← getMCtx -- save metavar context before using isDefEq
  let e_subexprs := getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return ← isDefEq e_subexpr subexpr)
  setMCtx mctx -- revert metavar context after using isDefEq, so this function doesn't have side-effects on the expr e
  return firstExprContainingSubexpr.isSome

/--This is the term that we are generalizing to an arbitrary term of that type -/
structure GeneralizedTerm where
  oldValue : Expr                 -- e.g. Hmul.hmul
  name : Name         := `f       -- e.g. f
  type : Expr                     -- e.g. ℕ → ℕ → ℕ
  placeholder : Expr              -- e.g. .mvar #2383...to uniquely identify where it is
deriving Repr

/- Given a theorem name n, returns the theorem statement with each instance of "p" -/
-- def replaceTheoremNameWithAbstractedTheoremStatement (n : Name) (p : Expr) : MetaM Expr :=
-- do


/- Replaces all instances of "p" in "e" with a metavariable.
Roughly implemented like kabstract, with the following differences:
  kabstract replaces "p" with a bvar, while this replaces "p" with an mvar
  kabstract replaces "p" with the same bvar, while this replaces each instance with a different mvar
  kabstract doesn't perform unification to make sure different mvars that will ultimately unify are this same, this does
  kabstract doesn't look for instances of "p" in the types of constants, this does
-/
partial def abstract (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  -- let e ← instantiateMVars e
  let pType ← inferType p
  -- let pHeadIdx := p.toHeadIndex
  -- let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) (offset : Nat) : StateRefT Nat MetaM Expr := do
    let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
      match e with
      -- unify types of metavariables as soon as we get a chance in .app
      -- that is, ensure that fAbs and aAbs are in sync about their metavariables
      | .app f a         =>
                            let fAbs ← visit f offset
                            let aAbs ← visit a offset
                            let .forallE _ fDomain _ _ ← inferType fAbs | throwError m!"Expected {fAbs} to have a `forall` type."
                            guard <| ← isDefEq fDomain (← inferType aAbs)
                            return e.updateApp! fAbs aAbs
      | .mdata _ b       => return e.updateMData! (← visit b offset)
      | .proj _ _ b      => return e.updateProj! (← visit b offset)
      | .letE _ t v b _  => return e.updateLet! (← visit t offset) (← visit v offset) (← visit b (offset+1))
      | .lam _ d b _     => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
      | .forallE _ d b _ => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
      -- when we encounter a theorem used in the proof
      -- check whether that theorem has the variable we're trying to generalize
      -- if it does, generalize the theorem accordingly, and make its proof an mvar.
      | .const n _       => let constType ← getTheoremStatement n
                            if (← containsExpr p constType) then
                              let genConstType ← visit constType offset -- expr for generalized proof statment
                              let m ← mkFreshExprMVar genConstType -- mvar for generalized proof
                              return m
                            else
                              return e
      | e                => logInfo "matched here"; return e

    if e.hasLooseBVars then
      logInfo m!"visiting children of {e} of type {e.ctorName}"
      visitChildren ()
    -- -- kabstract usually checks if the heads of the expressions are same before bothering to check definition equality
    -- -- this makes teh code more efficient, but it's not necessarily true that "heads not equal => not definitionally equal"
    -- else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
    --   visitChildren ()
    else
      logInfo m!"No loose bvars in {e}"
      -- We save the metavariable context here,
      -- so that it can be rolled back unless `occs.contains i`.
      let mctx ← getMCtx
      if (← isDefEq e p) then
        let i ← get
        set (i+1)
        if occs.contains i then
          let m ← mkFreshExprMVar pType -- replace every occurrence of pattern with mvar
          return m
        else
          -- Revert the metavariable context,
          -- so that other matches are still possible.
          setMCtx mctx
          visitChildren ()
      else
        visitChildren ()
  visit e 0 |>.run' 1

/-- Find the proof of the new auto-generalized theorem -/
def autogeneralizeProof (thmProof : Expr) (f : GeneralizedTerm) : MetaM Expr := do
  let abstractedProof ← abstract thmProof f.oldValue -- replace instances of f's old value with metavariables

  return abstractedProof


/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (fExpr : Expr): TacticM Unit := do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) := (← getHypothesisType thmName, ← getHypothesisProof thmName)

  -- Get details about the term we're going to generalize, to replace it with an arbitrary const of the same type
  let f : GeneralizedTerm := {oldValue := fExpr, name := `f, type := ← inferType fExpr, placeholder := ← mkFreshExprMVar (some (← inferType fExpr))}
  logInfo m!"The term to be generalized is {f.oldValue} with type {f.type}"

  -- -- Get the generalized theorem (with those additional hypotheses)
  let genThmProof ← autogeneralizeProof thmProof f; logInfo ("Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; logInfo ("Generalized Type: " ++ genThmType)
  let genThmType  ← instantiateMVars genThmType

  -- get the generalized type from user
  let userThmType ← kabstract thmType f.oldValue (occs:= .pos [1])
  let userThmType := userThmType.instantiate1 (← mkFreshExprMVar f.type)

  -- compare
  let unif ← isDefEq genThmType userThmType
  logInfo m!"Do they unify? {unif}"
  logInfo m!"Instantiated genThmType: {← instantiateMVars genThmType}"
  logInfo m!"Instantiated userThmType: {← instantiateMVars userThmType}"
  logInfo m!"Instantiated proof after type was inferred: {← instantiateMVars genThmProof}"

    -- turn mvars in abstracted proof into a lambda
  let mvarArray ← getMVars genThmProof
  let genThmProof ← mkLambdaFVars (mvarArray.map Expr.mvar) genThmProof (binderInfoForMVars := .default)
  -- let genThmProof ← mkForallFVars' (mvarArray.map Expr.mvar) genThmProof
  logInfo m!"Proof with fvars instead of mvars: {genThmProof}"
  let genThmType ← inferType genThmProof
  logInfo m!"Type with fvars instead of mvars: {genThmType}"

  createHypothesis genThmType genThmProof (thmName++`Gen)

  -- logInfo s!"Successfully generalized \n  {thmName} \nto \n  {thmName++`Gen} \nby abstracting \n  {← ppExpr fExpr}."

/- Autogeneralize term "t" in hypothesis "h"-/
elab "autogeneralize" h:ident f:term : tactic => do
  let f ← (Lean.Elab.Term.elabTerm f none)
  autogeneralize h.getId f

end Autogeneralize
