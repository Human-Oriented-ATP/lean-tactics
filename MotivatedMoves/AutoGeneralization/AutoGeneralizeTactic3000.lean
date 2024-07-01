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
      logInfo m!"this mvar {mvarId.name} contains mdata.  if it looks too big, it might be that the mvar with mdat has already been assigned {expr}"
      return mvarId
  throwError "No metavariable assigned to an expression with metadata found"

def getAssignmentFor (m : MVarId) : MetaM (Option Expr) := do
  let e ← getExprMVarAssignment? m
  return e

def getMVarContainingMData' (a : Array MVarId): MetaM MVarId := do
  for m in a do
    let m_assignment ← getAssignmentFor m
    if (m_assignment.isSome) then
      if(← containsMData (← m_assignment)) then
        --logInfo m!"this expr contains mdata.  if it looks too big, it might be that the mvar with mdat has already been assigned {m}"
        return m
    logInfo m!"found no assignment"
  throwError "No metavariable assigned to an expression with metadata found"

/-- Helper for incrementing idx when creating pretty names-/
-- partial def mkPrettyNameHelper(hypNames : List Name) (base : Name) (i : Nat) : Name :=
--   let candidate := base.appendIndexAfter i ++ `_gen
--   if (hypNames).contains candidate then
--     mkPrettyNameHelper hypNames base (i+1)
--   else
--     candidate

-- /-- Names a function baseName_idx if that is available.  otherwise, names it baseName_idx+1 if available...and so on. -/
-- def mkPrettyName (baseName : Name) : TacticM Name := do
--   return mkPrettyNameHelper (← getHypothesesNames) baseName 0

def mkAbstractedName (n : Name) : Name :=
    match n with
    | (.str _ s) => s!"gen_{s.takeWhile (fun c => c != '_')}" -- (fun c => c.isLower && c != '_')
    | _ => `unknown



/- Replaces all instances of "p" in "e" with a metavariable.
Roughly implemented like kabstract, with the following differences:
  kabstract replaces "p" with a bvar, while this replaces "p" with an mvar
  kabstract replaces "p" with the same bvar, while this replaces each instance with a different mvar
  kabstract doesn't look for instances of "p" in the types of constants, this does
  kabstract doesn't look under loose bvars, but this creates localdecls so we can still look under bvars
-/
partial def replacePatternWithMVars (e : Expr) (p : Expr) : MetaM Expr := do
  -- let e ← instantiateMVars e
  let (lctx, linst) := (← getLCtx, ← getLocalInstances)
  -- printLocalContext

  let pType ← inferType p
  -- the "depth" here is not depth of expression, but how many constants / theorems / inference rules we have unfolded
  let rec visit (e : Expr) (depth : ℕ := 0): MetaM Expr := do
    -- let e ← whnf e
    let visitChildren : Unit → MetaM Expr := fun _ => do
      match e with
      -- unify types of metavariables as soon as we get a chance in .app
      -- that is, ensure that fAbs and aAbs are in sync about their metavariables
      | .app f a         => let fAbs ← visit f depth
                            let aAbs ← visit a depth
                            -- check $ .app fAbs aAbs
                            return e.updateApp! fAbs aAbs
      | .mdata _ b       => return e.updateMData! (← visit b depth)
      | .proj _ _ b      => return e.updateProj! (← visit b depth)
      | .letE _ t v b _  => return e.updateLet! (← visit t depth) (← visit v depth) (← visit b depth)
      | .lam n d b bi     =>
                              let dAbs ← visit d depth
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedLambda ← withLocalDecl n bi dAbs (fun placeholder => do
                                let b := b.instantiate1 placeholder
                                let bAbs ← visit b depth-- now it's safe to recurse on b (no loose bvars)
                                return ← mkLambdaFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                              )
                              return updatedLambda
      | .forallE n d b bi => let dAbs ← visit d depth
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedForAll ← withLocalDecl n bi dAbs (fun placeholder => do
                                let b := b.instantiate1 placeholder
                                let bAbs ← visit b depth  -- now it's safe to recurse on b (no loose bvars)
                                return ← mkForallFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                              )
                              return updatedForAll
      -- when we encounter a theorem used in the proof
      -- check whether that theorem has the variable we're trying to generalize
      -- if it does, generalize the theorem accordingly, and make its proof an mvar.
      | .const n _       => let constType ← inferType e --getTheoremStatement n
                            if depth ≥ 1 then return e
                            else
                              if (← containsExpr p constType) then
                                let genConstType ← visit constType (depth+1)  -- expr for generalized proof statment
                                -- check genConstType
                                -- let genConstType ← instantiateMVars genConstType
                                let m ← mkFreshExprMVarAt lctx linst genConstType (kind := .synthetic) (userName := mkAbstractedName n)-- mvar for generalized proof
                                -- let m ← mkFreshExprMVar genConstType -- mvar for generalized proof
                                return m
                              else
                                return e
      | e                => return e

    if e.hasLooseBVars then
      visitChildren ()
    else
      -- We save the metavariable context here,
      -- so that it can be rolled back unless `occs.contains i`.
      let mctx ← getMCtx
      if (← isDefEq e p) then
        let m ← mkFreshExprMVarAt lctx linst pType (userName := `n) -- replace every occurrence of pattern with mvar
        -- let m ← mkFreshExprMVar pType -- replace every occurrence of pattern with mvar
        return m
      else
        -- Revert the metavariable context,
        -- so that other matches are still possible.
        setMCtx mctx
        visitChildren ()
  visit e


/-- Find the proof of the new auto-generalized theorem -/
def autogeneralizeProof (thmProof : Expr) (fExpr : Expr) : MetaM Expr := do
  -- Get the generalized theorem (replace instances of fExpr with mvars, and unify mvars where possible)
  let abstractedProof ← replacePatternWithMVars thmProof fExpr -- replace instances of f's old value with metavariables
  -- let abstractedProof ← kabstract thmProof fExpr -- replace instances of f's old value with metavariables
  -- let abstractedProof := abstractedProof.instantiate1 (← mkFreshExprMVar (← inferType fExpr))
  -- logInfo m!"abstracted "

  -- logInfo m!"Generalized proof before linking mvars {abstractedProof}"

  -- unify "linked" mvars in proof
  check abstractedProof
  let abstractedProof ← instantiateMVars abstractedProof

  return abstractedProof

def abstractToDiffMVars (thmType : Expr) (fExpr : Expr) (occs : Occurrences) : MetaM Expr := do
  return ← kabstract thmType fExpr (occs)
  -- match occs with
  -- | .all =>
  --     let mut thmType := thmType
  --     while (← containsExpr thmType fExpr) do
  --       thmType ← kabstract thmType fExpr (.pos [1])
  --     return thmType
  -- | .pos idx =>
  --     let mut thmType := thmType
  --     for i in idx do
  --       thmType ← kabstract thmType fExpr (.pos [i])
  --     logInfo m!"abstractToDiffMVars: we have now abstracted thmtype {thmType}"
  --     return thmType
  -- | .neg _ => throwError "Putting in negative occurrences is not supported in this tactic."

def abstractToOneMVar (thmType : Expr) (fExpr : Expr) (occs : Occurrences) : MetaM Expr := do
  return ← kabstract thmType fExpr (occs)

/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (fExpr : Expr) (occs : Occurrences := .pos [1]) (consolidate : Bool := false) : TacticM Unit := withMainContext do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) := (← getHypothesisType thmName, ← getHypothesisProof thmName)

  -- logInfo ("Ungeneralized Proof: " ++ thmProof)

  -- Get details about the term we're going to generalize, to replace it with an arbitrary const of the same type
  -- logInfo m!"The term to be generalized is {fExpr} with type {← inferType fExpr}"

  let mut genThmProof := thmProof
  -- let genThmProof := thmProof
  -- while ← containsExpr fExpr thmProof do
  genThmProof ←  autogeneralizeProof thmProof fExpr; logInfo ("Tactic Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; logInfo ("!Tactic Generalized Type: " ++ genThmType)

  -- Get the generalized type from user
  -- to do -- should also generalize any other occurrences in the type that unify with other occurrences in the type.

  let userThmType ← if consolidate then
    abstractToOneMVar thmType fExpr occs
  else
    abstractToDiffMVars thmType fExpr occs

  let mvarsInProof := (← getMVars genThmProof) ++ (← getMVars genThmType)


  let userMVar ←  mkFreshExprMVar (← inferType fExpr)
  let annotatedMVar := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ userMVar
  let userThmType := userThmType.instantiate1 annotatedMVar
  --logInfo m!"!User Generalized Type: {userThmType}"

  -- compare and unify mvars between user type and our generalized type
  let unif ← isDefEq  genThmType userThmType
  --logInfo m!"Do they unify? {unif}"

  let userSelectedMVar ← getMVarContainingMData' mvarsInProof
  --logInfo m!"Mvars containing mdata {userSelectedMVar.name} with {userSelectedMVar}"
  if !(← userMVar.mvarId!.isAssigned) then
    try
      userMVar.mvarId!.assignIfDefeq (.mvar userSelectedMVar)
    catch _ =>
      throwError m!"Tried to assign mvars that are not defeq {userSelectedMVar} and {userMVar}"

  genThmProof  ←  instantiateMVarsExcept userSelectedMVar genThmProof

  -- remove repeating hypotheses: if any of the mvars have the same type (but not pattern type), unify them

  let hyps ← getMVars genThmProof
  for hyp1 in hyps do
    let mctx ← getMCtx
    let repeatingHyp ← hyps.findM? (fun hyp2 => return hyp1 != hyp2 && (← isDefEq (← hyp1.getType) (← hyp2.getType)) && !(← hyp2.isAssigned))
    setMCtx mctx
    if repeatingHyp.isSome then
      let repeatingHyp ← repeatingHyp
      try
        if !(← repeatingHyp.isAssigned) then do
          hyp1.assignIfDefeq (.mvar repeatingHyp)
      catch _ =>
        throwError m!"Tried to assign mvars that are not defeq {hyp1.name} with {← hyp1.getType} and {repeatingHyp.name} with {← repeatingHyp.getType}"

  -- genThmProof ← instantiateMVars genThmProof

  -- Get new mvars (the abstracted fExpr & all hypotheses on it), then pull them out into a chained implication
  genThmProof := (← abstractMVars genThmProof).expr; --logInfo ("Tactic Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; --logInfo ("Tactic Generalized Type: " ++ genThmType)

  createLetHypothesis genThmType genThmProof (thmName++`Gen)

  logInfo s!"Successfully generalized \n  {thmName} \nto \n  {thmName++`Gen} \nby abstracting {← ppExpr fExpr}."

syntax occurrences :="at" "occurrences" "[" num+ "]"

def decodeOccurrences : TSyntax `Autogeneralize.occurrences → List Nat
  | `(occurrences| at occurrences [$occs*]) => (occs.map TSyntax.getNat).toList
  | _ => unreachable!


/- Autogeneralize term "pattern" in hypothesis "h" -/
elab "autogeneralize" pattern:term "in" h:ident occs:(Autogeneralize.occurrences)? : tactic => do
  let pattern ← (Lean.Elab.Term.elabTerm pattern none)
  let h := h.getId
  let occs := occs.map decodeOccurrences
  -- logInfo m!"Automatically generalizing the occurrences {occs} of the pattern {pattern} in {h} ..."
  if occs.isSome then
    autogeneralize h pattern (Occurrences.pos $ ← occs)
  else
    autogeneralize h pattern --(.all) -- generalize all occurrences (default: to different mvars)


/-  Autogeneralize term "pattern" in hypothesis "h", but generalize all occurrences.
    Behaves as in (Pons, 2000 )
    Either "naive_autogeneralize" or "basic_autogeneralize" or "autogeneralize_v0"
    Maybe autogeneralize vs autogenerlize+
    Or autogeneralize_all vs autogeneralize_linked / autogeneralize_selective
-/
elab "autogeneralize_basic" pattern:term "in" h:ident occs:(Autogeneralize.occurrences)? : tactic => do
  let pattern ← (Lean.Elab.Term.elabTerm pattern none)
  let h := h.getId
  let occs := occs.map decodeOccurrences
  autogeneralize h pattern (occs:=.all) (consolidate:=true)

end Autogeneralize
