import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/
import Mathlib.Data.Real.Irrational

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize

/-- Getting theorems from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | throwError ("Could not find a theorem with name " ++ n) -- get the declaration with that name
  return thm.type -- return the theorem statement (the type is the proposition)

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

/-- Create a new hypothesis using a "have" statement -/
def createHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  let hyp : Hypothesis := { userName := hypName, type := hypType, value := hypProof }
  let check ← isDefEq (hypType) (← inferType hypProof)
  if !check then throwError "Hypothesis type {hypType} doesn't match proof {hypProof}"
  let (_, new_goal) ← (←getGoalVar).assertHypotheses (List.toArray [hyp])
  setGoals [new_goal]

/-- Create a new hypothesis using a "let" statement (so its proof is accessible)-/
def createLetHypothesis (hypType : Expr) (hypProof : Expr) (hypName? : Option Name := none) : TacticM Unit := do
  let hypName := hypName?.getD `h -- use the name given first, otherwise call it `h
  let check ← isDefEq (hypType) (← inferType hypProof)
  if !check then throwError "Hypothesis type {hypType} doesn't match proof {hypProof}"
  let new_goal ← (←getGoalVar).define hypName hypType hypProof
  let (_, new_goal) ← intro1Core new_goal true
  setGoals [new_goal]

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

/-- Returns true if "e" contains "subexpr".  Differs from "occurs" because this uses the coarser "isDefEq" rather than "==" -/
def containsExpr(subexpr : Expr)  (e : Expr) : MetaM Bool := do
  let mctx ← getMCtx -- save metavar context before using isDefEq
  let e_subexprs := getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return ← isDefEq e_subexpr subexpr)
  setMCtx mctx -- revert metavar context after using isDefEq, so this function doesn't have side-effects on the expr e
  return firstExprContainingSubexpr.isSome

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

#check kabstract

#check Exception

partial def replacePatternWithMVars (e : Expr) (p : Expr) : MetaM Expr := do
  -- let e ← instantiateMVars e

  let pType ← inferType p
  -- let pHeadIdx := p.toHeadIndex
  -- let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) : StateRefT Nat MetaM Expr := do
    -- let e ← whnf e
    let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
      match e with
      -- unify types of metavariables as soon as we get a chance in .app
      -- that is, ensure that fAbs and aAbs are in sync about their metavariables
      | .app f a         => let fAbs ← visit f
                            let aAbs ← visit a
                            -- reducible transparency lets you see that reducible types that don't seem like forall statements actually are forall statements
                            let t  ← whnf $ ← inferType fAbs
                            let .forallE _ fDomain _ _ := t | throwError m!"yyExpected {fAbs} to have a `forall` type in {e} with body of type {t}."
                            -- if !aAbs.hasLooseBVars  then
                            let aAbsType ← inferType aAbs
                            unless ← isDefEq fDomain aAbsType do
                              logInfo m!"The domain of the function application: {fDomain}"
                              logInfo m!"The type of the argument: {aAbsType}"
                              throwError m!"Defeq failed on comparing the domain and argument type on {e}."

                            return e.updateApp! fAbs aAbs
      | .mdata _ b       => return e.updateMData! (← visit b)
      | .proj _ _ b      => return e.updateProj! (← visit b)
      | .letE _ t v b _  => return e.updateLet! (← visit t) (← visit v) (← visit b)
      | .lam n d b bi     =>
                            let dAbs ← visit d
                            --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                            let updatedLambda ← withLocalDecl n .default dAbs (fun placeholder => do
                              let b := b.instantiate1 placeholder
                              let bAbs ← visit b -- now it's safe to recurse on b (no loose bvars)
                              return ← mkLambdaFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                            )
                            return updatedLambda
      | .forallE n d b bi => let dAbs ← visit d
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedForAll ← withLocalDecl n .default dAbs (fun placeholder => do
                                let b := b.instantiate1 placeholder
                                let bAbs ← visit b  -- now it's safe to recurse on b (no loose bvars)
                                return ← mkForallFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                              )
                              return updatedForAll
      -- when we encounter a theorem used in the proof
      -- check whether that theorem has the variable we're trying to generalize
      -- if it does, generalize the theorem accordingly, and make its proof an mvar.
      | .const n _       => let constType ← getTheoremStatement n
                            if (← containsExpr p constType) then
                              let genConstType ← visit constType  -- expr for generalized proof statment
                              let m ← mkFreshExprMVar genConstType -- mvar for generalized proof
                              return m
                            else
                              return e
      | e                => return e

    if e.hasLooseBVars then
      -- logInfo m!"loose bvars found in {e}"
      visitChildren ()
    -- -- kabstract usually checks if the heads of the expressions are same before bothering to check definition equality
    -- -- this makes teh code more efficient, but it's not necessarily true that "heads not equal => not definitionally equal"
    -- else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
    --   visitChildren ()
    else
      -- We save the metavariable context here,
      -- so that it can be rolled back unless `occs.contains i`.
      let mctx ← getMCtx
      if (← isDefEq e p) then
        let m ← mkFreshExprMVar pType -- replace every occurrence of pattern with mvar
        return m
      else
        -- Revert the metavariable context,
        -- so that other matches are still possible.
        setMCtx mctx
        visitChildren ()
  visit e |>.run' 1

/-- Find the proof of the new auto-generalized theorem -/
def autogeneralizeProof (thmProof : Expr) (fExpr : Expr) : MetaM Expr := do
  -- deal with case where all your "foralls" are in the front of the clause
  -- that is, replace bound variables with mvars
  -- let (mvars, _binders, thmProof) ← lambdaMetaTelescope thmProof
  -- logInfo m!"Telescoped theorem proof {thmProof}"

  -- Get the generalized theorem (replace instances of fExpr with mvars, and unify mvars where possible)
  let abstractedProof ← replacePatternWithMVars thmProof fExpr -- replace instances of f's old value with metavariables


  return abstractedProof

/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (fExpr : Expr): TacticM Unit := do

  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) := (← getHypothesisType thmName, ← getHypothesisProof thmName)

  logInfo ("Ungeneralized Proof: " ++ thmProof)

  -- Get details about the term we're going to generalize, to replace it with an arbitrary const of the same type
  logInfo m!"The term to be generalized is {fExpr} with type {← inferType fExpr}"

  let genThmProof ← autogeneralizeProof thmProof fExpr; logInfo ("Tactic Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; logInfo ("Tactic Generalized Type: " ++ genThmType)

  -- Get the generalized type from user
  let userThmType ← kabstract thmType fExpr (occs:= .pos [1]) -- generalize the first occurrence of the expression in the type
  let userThmType := userThmType.instantiate1 (← mkFreshExprMVar (← inferType fExpr))
  logInfo m!"User Generalized Type: {userThmType}"

  -- compare and unify mvars
  -- let mctx ← getMCtx
  let unif ← isDefEq genThmType userThmType
  logInfo m!"Do they unify? {unif}"
  -- setMCtx mctx


  let genThmType  ← instantiateMVars genThmType
  let genThmProof  ← instantiateMVars genThmProof
  -- logInfo m!"Instantiated genThmType: {genThmType}"
  -- logInfo m!"Instantiated userThmType: {userThmType}"

     -- Get new mvars (the abstracted fExpr & all hypotheses on it)
  let mvarArray ← getMVars genThmProof
 -- Turn the abstracted fExpr & all hypotheses into a chained implication
  let genThmProof ← mkLambdaFVars (mvarArray.map Expr.mvar) genThmProof (binderInfoForMVars := .default)
  let genThmType ← inferType genThmProof; logInfo ("Tactic Generalized Type: " ++ genThmType)

  logInfo m!"Instantiated proof after type was inferred: {genThmProof}"



  -- let genThmType ← inferType genThmProof
  -- logInfo m!"Type with fvars instead of mvars: {genThmType}"

  createLetHypothesis genThmType genThmProof (thmName++`Gen)

  logInfo s!"Successfully generalized \n  {thmName} \nto \n  {thmName++`Gen} \nby abstracting \n  {← ppExpr fExpr}."

/- Autogeneralize term "t" in hypothesis "h"-/
elab "autogeneralize" h:ident f:term : tactic => do
  let f ← (Lean.Elab.Term.elabTerm f none)
  autogeneralize h.getId f

end Autogeneralize
