import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/
import Mathlib.Data.Real.Irrational

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize

def printMVarAssignments : MetaM Unit := do
  let m ← getMCtx
  dbg_trace "MVar Assingnments:"
  for d in m.eAssignment do
    let mvarId := d.fst
    let assignment := d.snd
    logInfo s!"\tName: {mvarId.name} \n\tAssignment: {assignment}\n"


def removeAssignment (mv : MVarId) : MetaM Unit := do
  -- remove the assignment
  let mctx ← getMCtx
  let mctxassgn := mctx.eAssignment.erase mv
  setMCtx {mctx with eAssignment := mctxassgn} -- mctxassgn

/- Instantiates all mvars in e except the mvar given by the array a -/
def instantiateMVarsExcept (a : Array MVarId) (e : Expr)  : MetaM Expr := do
  for mv in a do
   removeAssignment mv -- remove the assignment
  let e ← instantiateMVars e -- instantiate mvars
  return e

def getHypothesesMeta : MetaM (List LocalDecl) := do
  let mut hypotheses : List LocalDecl := []
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    hypotheses := ldecl :: hypotheses
  return hypotheses

def getHypothesesNamesMeta : MetaM (List Name) := do
    return (← getHypothesesMeta).map (fun hypothesis => hypothesis.userName)


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
    -- | Expr.letE _ t v b _    => [e] ++ (getSubexpressionsInRec t acc) ++ (getSubexpressionsInRec v acc) ++ (getSubexpressionsInRec b acc)
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

def getAssignmentFor (m : MVarId) : MetaM (Option Expr) := do
  let e ← getExprMVarAssignment? m
  return e

def assignmentContainsMData (m : MVarId) : MetaM Bool := do
  let m_assignment ← getAssignmentFor m
  if (m_assignment.isSome) then
    if (← containsMData (← m_assignment)) then
      return True
  return False

def getAllMVarsContainingMData (a : Array MVarId): MetaM (Array MVarId) :=
   a.filterM assignmentContainsMData


def getMVarContainingMData' (a : Array MVarId): MetaM MVarId := do
  for m in a do
    let m_assignment ← getAssignmentFor m
    if (m_assignment.isSome) then
      if(← containsMData (← m_assignment)) then
        --logInfo m!"this expr contains mdata.  if it looks too big, it might be that the mvar with mdat has already been assigned {m}"
        return m
  throwError "No metavariable assigned to an expression with metadata found"

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
-- NOTE (future TODO): this code can now be rewritten without `withLocalDecl` or `mkFreshExprMVarAt`
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
        let m ← mkFreshExprMVarAt lctx linst pType --(userName := `n) -- replace every occurrence of pattern with mvar
        -- let m ← mkFreshExprMVar pType -- replace every occurrence of pattern with mvar
        return m
      else
        -- Revert the metavariable context,
        -- so that other matches are still possible.
        setMCtx mctx
        visitChildren ()
  visit e




def abstractToDiffMVars (e : Expr) (p : Expr) (occs : Occurrences) : MetaM Expr := do
  let pType ← inferType p

  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) : StateRefT Nat MetaM Expr := do
    let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
      match e with
      | .app f a         => return e.updateApp! (← visit f ) (← visit a )
      | .mdata _ b       => return e.updateMData! (← visit b )
      | .proj _ _ b      => return e.updateProj! (← visit b )
      | .letE _ t v b _  => return e.updateLet! (← visit t ) (← visit v ) (← visit b )
      | .lam _ d b _     => return e.updateLambdaE! (← visit d ) (← visit b )
      | .forallE _ d b _ => return e.updateForallE! (← visit d ) (← visit b )
      | e                => return e
    if e.hasLooseBVars then
      visitChildren ()
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren ()
    else
      -- We save the metavariable context here,
      -- so that it can be rolled back unless `occs.contains i`.
      let mctx ← getMCtx
      if (← isDefEq e p) then
        let i ← get
        set (i+1)
        if occs.contains i then
          let userMVar ← mkFreshExprMVar pType
          let annotatedMVar := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ userMVar
          return annotatedMVar
        else
          -- Revert the metavariable context,
          -- so that other matches are still possible.
          setMCtx mctx
          visitChildren ()
      else
        visitChildren ()
  visit e |>.run' 1



def abstractToOneMVar (thmType : Expr) (pattern : Expr) (occs : Occurrences) : MetaM Expr := do
  let userThmType ← kabstract thmType pattern (occs)

  let userMVar ←  mkFreshExprMVar (← inferType pattern)
  let annotatedMVar := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ userMVar
  let userThmType := userThmType.instantiate1 annotatedMVar

  return userThmType

/- Make all mvars in mvarArray with the type t the same  -/
def setEqualAllMVarsOfType (mvarArray : Array MVarId) (t : Expr) : MetaM Unit := do
  let m ← mkFreshExprMVar t -- new mvar to replace all others with the same type
  for mv in mvarArray do
    if ← isDefEq (← mv.getType) t then
      if !(← mv.isAssigned) then mv.assignIfDefeq m

/- Unifies metavariables (which are hypotheses) when possible.  -/
def removeRepeatingHypotheses (genThmProof : Expr) : MetaM Expr := do
  let hyps ← getMVars genThmProof
  for hyp₁ in hyps do
    for hyp₂ in hyps do
      -- performs unificiation on propositions
      if (← isProp <| ← hyp₁.getType') then do
        -- `discard` ignores the result of its argument (but retains modifications to the state)
        -- `isDefEq` automatically rejects cases where the meta-variables have different types or have conflicting assignments
        discard <| isDefEq (.mvar hyp₁) (.mvar hyp₂)
  return genThmProof

-- def respecializeOccurrences (thmType : Expr) (genThmProof : Expr) (pattern : Expr) (occsToStayAbstracted : Occurrences) (consolidate : Bool) : MetaM Expr := do

--   -- Get the occurrences of the pattern (in the theorem statement) the user wants to specialize
--   let userThmType ← if consolidate then
--     abstractToOneMVar thmType pattern occsToStayAbstracted
--   else
--     abstractToDiffMVars thmType pattern occsToStayAbstracted
--   logInfo m!"!User Generalized Type: {userThmType}"

--   -- Compare and unify mvars between user type and our generalized type
--   let genThmType ← inferType genThmProof
--   let _ ← isDefEq  genThmType userThmType

--   -- Instantiate the ones we don't want to generalize
--   let mvarsInProof := (← getMVars genThmProof) ++ (← getMVars genThmType)
--   let userSelectedMVars ← getAllMVarsContainingMData mvarsInProof
--   return ← instantiateMVarsExcept userSelectedMVars genThmProof

def performSimp (genThmType : Expr ) (genThmProof : Expr ): MetaM (Expr × Expr) := do
  let (result, _) ← Lean.Meta.simp genThmType {}
  let genThmTypeSimp := result.expr
  let genThmProofSimp ← mkAppM `Eq.mpr #[← result.getProof, genThmProof]
  return (genThmTypeSimp, genThmProofSimp)

/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (pattern : Expr) (occs : Occurrences := .all) (consolidate : Bool := false) : TacticM Unit := withMainContext do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) := (← getHypothesisType thmName, ← getHypothesisProof thmName)

  let mut genThmProof := thmProof

  -- Get the generalized theorem (replace instances of pattern with mvars, and unify mvars where possible)
  genThmProof ← replacePatternWithMVars thmProof pattern -- replace instances of f's old value with metavariables
  -- genThmProof ← kabstract thmProof pattern -- replace instances of f's old value with metavariables
  -- genThmProof := genThmProof.instantiate1 (← mkFreshExprMVar (← inferType pattern))

  try
    check genThmProof
  catch e =>
    throwError "The type of the proof doesn't match the statement.  Perhaps a computation rule was used?"
  genThmProof ← instantiateMVars genThmProof
  let genThmType ← inferType genThmProof

  -- Re-specialize the occurrences of the pattern we are not interested in
  if !(occs == .all) then do
    -- genThmProof ← respecializeOccurrences thmType genThmProof pattern (occsToStayAbstracted := occs) consolidate
    -- logInfo m!"!Tactic Generalized Type After Unifying: {← inferType genThmProof}"
    let userThmType ← if consolidate then
      abstractToOneMVar thmType pattern occs
    else
      abstractToDiffMVars thmType pattern occs

    let mvarsInProof := (← getMVars genThmProof) ++ (← getMVars genThmType)

    logInfo m!"!User Generalized Type: {userThmType}"

    -- compare and unify mvars between user type and our generalized type
    let unif ← isDefEq  genThmType userThmType
    --logInfo m!"Do they unify? {unif}"

    let userSelectedMVars ← getAllMVarsContainingMData mvarsInProof
    -- for m in userSelectedMVars do
    --   logInfo m.name
    -- printMVarAssignments
    --logInfo m!"Mvars containing mdata {userSelectedMVar.name} with {userSelectedMVar}"
    -- for userMVar in userSelectedMVars do
    -- if !(← userMVar.mvarId!.isAssigned) then
    --   try
    --     userMVar.mvarId!.assignIfDefeq (.mvar userSelectedMVar)
    --   catch _ =>
    --     throwError m!"Tried to assign mvars that are not defeq {userSelectedMVar} and {userMVar}"

    genThmProof  ←  instantiateMVarsExcept userSelectedMVars genThmProof

  -- (If desired) make all abstracted instances of the pattern the same.
  if consolidate then do
    let mvarsInProof := (← getMVars genThmProof) ++ (← getMVars genThmType)
    setEqualAllMVarsOfType mvarsInProof (← inferType pattern)

  -- remove hypotheses not involving the mvar
  -- this happens only when we specialize only at occurrences
  -- which means we pull out hypotheses involving other occurrences, but then re-specialize them
  -- so we don't need an extra hyp
  -- let hyps ← getMVars genThmProof
  -- for hyp in hyps do
  --   if

  -- Remove repeating hypotheses.
  genThmProof ← removeRepeatingHypotheses genThmProof

  -- Pull out the holes (the abstracted term & all hypotheses on it) into a chained implication.
  genThmProof := (← abstractMVars genThmProof).expr; --logInfo ("Tactic Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; --logInfo ("Tactic Generalized Type: " ++ genThmType)

  -- Run "simp".
  let (genThmTypeSimp, genThmProofSimp) ← performSimp genThmType genThmProof

  -- Add the generalized theorem to the context.
  createLetHypothesis genThmTypeSimp genThmProofSimp (thmName++`Gen)

  logInfo s!"Successfully generalized \n  {thmName} \nto \n  {thmName++`Gen} \nby abstracting {← ppExpr pattern}."

/--
Parse occurrences of the term as specified by the user.
-/
syntax occurrences :="at" "occurrences" "[" num+ "]"
def decodeOccurrences : TSyntax `Autogeneralize.occurrences → List Nat
  | `(occurrences| at occurrences [$occs*]) => (occs.map TSyntax.getNat).toList
  | _ => unreachable!

/--
Autogeneralizes the "pattern" in the hypothesis "h",
Default behavior is to generalizes all occurrences separately, but can generalize at specified occurences.
-/
elab "autogeneralize" pattern:term "in" h:ident occs:(Autogeneralize.occurrences)? : tactic => do
  let pattern ← (Lean.Elab.Term.elabTerm pattern none)
  let h := h.getId
  let occs := occs.map decodeOccurrences
  if occs.isSome then
    autogeneralize h pattern (Occurrences.pos $ ← occs)
  else
    autogeneralize h pattern -- generalize all occurrences (default: to different mvars)


/--
Autogeneralizes the "pattern" in the hypothesis "h",
But generalizes all occurrences in the same way.  Behaves as in (Pons, 2000)
-/
elab "autogeneralize_basic" pattern:term "in" h:ident : tactic => do
  let pattern ← (Lean.Elab.Term.elabTerm pattern none)
  let h := h.getId
  autogeneralize h pattern (occs:=.all) (consolidate:=true)

end Autogeneralize
