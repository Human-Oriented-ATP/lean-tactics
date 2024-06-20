import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/
import Mathlib.Data.Real.Irrational

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize

def printMVarsAssignmentsInContext : MetaM Unit := do
  let m ← getMCtx
  logInfo m!"MVar Context:
    {(m.eAssignment.toList.map (fun d =>
    m!"Mvar:
      {d.fst.name}
    Assignment:
      {repr d.snd}"

  ))}"

def printMVarContext : MetaM Unit := do
  let m ← getMCtx
  logInfo m!"MVar Context: {(m.decls.toList.map (fun d =>
    m!"Name: {d.fst.name} Kind:{repr d.snd.kind} "
  ))}"

def printLocalContext : MetaM Unit := do
  let (lctx, linst) := (← getLCtx, ← getLocalInstances)
  logInfo m!"Local context {lctx.decls.toList.filterMap (fun oplocdec => oplocdec.map (LocalDecl.userName))}"
  logInfo m!"Local instances {linst.map LocalInstance.className}"


/- Instantiates all mvars in e except the mvar given by m -/
def instantiateMVarsExcept (mv : MVarId) (e : Expr)  : MetaM Expr := do
  -- remove the assignment
  let mctx ← getMCtx
  let mctxassgn := mctx.eAssignment.erase mv
  setMCtx {mctx with eAssignment := mctxassgn} -- mctxassgn
  -- instantiate mvars
  -- let e ← instantiateMVars e
  return e


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

/- Replaces all subexpressions where "condition" holds with the "replacement" in the expression e -/
def containsExprWhere (condition : Expr → Bool) (e : Expr)   : MetaM Bool := do
  let e_subexprs := getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return condition e_subexpr)
  return firstExprContainingSubexpr.isSome


def containsMData (e : Expr): MetaM Bool := do
  return ← containsExprWhere (Expr.isMData) e

def getMVarAssignedToMData : MetaM MVarId := do
  let mctx ← getMCtx
  for (mvarId, expr) in mctx.eAssignment do
    if Expr.isMData expr then
      return mvarId
  throwError "No metavariable assigned to an expression with metadata found"

def getMVarContainingMData : MetaM MVarId := do
  let mctx ← getMCtx
  for (mvarId, expr) in mctx.eAssignment do
    if ← containsMData expr then
      return mvarId
  throwError "No metavariable assigned to an expression with metadata found"


/- Replaces all instances of "p" in "e" with a metavariable.
Roughly implemented like kabstract, with the following differences:
  kabstract replaces "p" with a bvar, while this replaces "p" with an mvar
  kabstract replaces "p" with the same bvar, while this replaces each instance with a different mvar
  kabstract doesn't perform unification to make sure different mvars that will ultimately unify are this same, this does
  kabstract doesn't look for instances of "p" in the types of constants, this does
-/
partial def replacePatternWithMVars (e : Expr) (p : Expr) : MetaM Expr := do
  -- let e ← instantiateMVars e
  let (lctx, linst) := (← getLCtx, ← getLocalInstances)
  -- printLocalContext

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
                            check $ .app fAbs aAbs
                            return e.updateApp! fAbs aAbs
      | .mdata _ b       => return e.updateMData! (← visit b)
      | .proj _ _ b      => return e.updateProj! (← visit b)
      | .letE _ t v b _  => return e.updateLet! (← visit t) (← visit v) (← visit b)
      | .lam n d b bi     =>
                            -- if bi.isInstImplicit then
                            --   let updatedLambda ← lambdaTelescope e (fun fvars b => do
                            --     let placeholder := fvars[0]!
                            --     let b := b.instantiate1 placeholder
                            --     let bAbs ← visit b -- now it's safe to recurse on b (no loose bvars)
                            --     return ← mkLambdaFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                            --   )
                            --   return updatedLambda
                            -- else
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
      | .const n _       => let constType ← inferType e --getTheoremStatement n
                            if (← containsExpr p constType) then
                              let genConstType ← visit constType  -- expr for generalized proof statment
                              let m ← mkFreshExprMVarAt lctx linst genConstType (kind := .synthetic)-- mvar for generalized proof
                              -- let m ← mkFreshExprMVar genConstType -- mvar for generalized proof
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
        let m ← mkFreshExprMVarAt lctx linst pType -- replace every occurrence of pattern with mvar
        -- let m ← mkFreshExprMVar pType -- replace every occurrence of pattern with mvar
        return m
      else
        -- Revert the metavariable context,
        -- so that other matches are still possible.
        setMCtx mctx
        visitChildren ()
  visit e |>.run' 1
  -- check e
  -- return ← instantiateMVars e

/-- Find the proof of the new auto-generalized theorem -/
def autogeneralizeProof (thmProof : Expr) (fExpr : Expr) : MetaM Expr := do
  -- Get the generalized theorem (replace instances of fExpr with mvars, and unify mvars where possible)
  let abstractedProof ← replacePatternWithMVars thmProof fExpr -- replace instances of f's old value with metavariables
  -- let abstractedProof ← liftTermElabM synthesizeSyntheticMVarsNoPostponing abstractedProof
  -- let abstractedProof ← unifyMVars abstractedProof
  return abstractedProof

/-- Get all mvars in an expression, as well as all mvars that each mvar depends on. -/
def getMVarsRecursive (e : Expr) : MetaM (Array MVarId) := do
  let mvars : Array MVarId ← getMVars e

  let mut allMVars : Array MVarId := mvars
  for mvar in mvars do
    let deps := (← mvar.getMVarDependencies).toArray
    allMVars := allMVars ++ deps

  return allMVars.toList.eraseDups.toArray

-- def withAssignableSyntheticOpaque : MetaM α → MetaM α :=
--   withReader (fun ctx => {ctx with config := {ctx.config with assignSyntheticOpaque := true}} )

deriving instance Repr for Occurrences
/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (fExpr : Expr) (occs : Occurrences := .pos [1]) : TacticM Unit := withMainContext do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) := (← getHypothesisType thmName, ← getHypothesisProof thmName)

  logInfo ("Ungeneralized Proof: " ++ thmProof)

  -- Get details about the term we're going to generalize, to replace it with an arbitrary const of the same type
  logInfo m!"The term to be generalized is {fExpr} with type {← inferType fExpr}"



  -- let genThmProof := thmProof
  -- while ← containsExpr fExpr thmProof do
  let genThmProof ←  autogeneralizeProof thmProof fExpr; logInfo ("Tactic Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; logInfo ("!Tactic Generalized Type: " ++ genThmType)

  -- Get the generalized type from user
  -- to do -- should also generalize any other occurrences in the type that unify with other occurrences in the type.
  let userThmType ← kabstract thmType fExpr occs -- generalize the first occurrence of the expression in the type

  -- let _ ← withLocalDecl `userSelected .default (← inferType fExpr) (fun placeholder => do
    -- return ← mkLambdaFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
  -- withNewMCtxDepth do
  let userMVar ←  mkFreshExprMVar (← inferType fExpr)
  let annotatedMVar := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ userMVar
  let userThmType := userThmType.instantiate1 annotatedMVar
  logInfo m!"!User Generalized Type: {userThmType}"
  logInfo m!"mvars in user type {(← getMVars userThmType).map MVarId.name}"
  logInfo m!"mvars in gen type {(← getMVars genThmType).map MVarId.name}"

  -- compare and unify mvars between user type and our generalized type
  let unif ← isDefEq  genThmType userThmType
  logInfo m!"Do they unify? {unif}"

  -- logInfo m!"User Type with instantiated mvars: {← instantiateMVars userThmType}"
  -- logInfo m!"Gen Type with instantiated mvars: {← instantiateMVars genThmType}"
  -- logInfo m!"Proof with instantiated mvars: {← instantiateMVars  genThmProof}"
  logInfo m!"mvars in gen proof {(← getMVars genThmProof).map MVarId.name}"

  let userSelectedMVar ← getMVarContainingMData
  if !(← userMVar.mvarId!.isAssigned) then
    userMVar.mvarId!.assignIfDefeq (.mvar userSelectedMVar)

  logInfo m!"assingned mvar {userSelectedMVar.name}"
  let genThmProof  ←  instantiateMVarsExcept userSelectedMVar genThmProof
  logInfo m!"Proof with reabstracted mvars: {genThmProof}"
  logInfo m!"mvars in rebastracted proof {(← getMVars genThmProof).map MVarId.name}"

  -- logInfo m!"Type with instantiated mvars: {userThmType}"

  -- Get new mvars (the abstracted fExpr & all hypotheses on it), then pull them out into a chained implication
  let genThmProof := (← abstractMVars genThmProof).expr; logInfo ("Tactic Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; logInfo ("Tactic Generalized Type: " ++ genThmType)
  createLetHypothesis genThmType genThmProof (thmName++`Gen)

  logInfo s!"Successfully generalized \n  {thmName} \nto \n  {thmName++`Gen} \nby abstracting \n  {← ppExpr fExpr}."

  -- )


def elabOccs (occs : Option $ TSyntax `Lean.Parser.Tactic.Conv.occs) : MetaM Occurrences := do
  match occs with
    | none => pure (.pos [])
    | some occs => match occs with
      | `(Parser.Tactic.Conv.occsWildcard| *) => pure .all
      | `(Parser.Tactic.Conv.occsIndexed| $ids*) => do
        let ids ← ids.mapIdxM fun i id =>
          match id.getNat with
          | 0 => throwErrorAt id "positive integer expected"
          | n+1 => pure (n+1, i.1) -- the occurrences & list index
        let ids := ids.qsort (·.1 < ·.1)
        unless @Array.allDiff _ ⟨(·.1 == ·.1)⟩ ids do
          throwError "occurrence list is not distinct"
        pure (.pos $ ids.toList.map (·.1)) -- get just the occurrences
      | _ => throwUnsupportedSyntax

/- Autogeneralize term "t" in hypothesis "h"-/
elab "autogeneralize" h:ident f:term : tactic => do
  let f ← (Lean.Elab.Term.elabTerm f none)
  autogeneralize h.getId f

end Autogeneralize
