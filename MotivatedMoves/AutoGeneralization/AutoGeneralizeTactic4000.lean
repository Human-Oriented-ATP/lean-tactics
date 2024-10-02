import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/
import Mathlib.Data.Real.Irrational

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize

/-- Remove the assignment of a metavariable from the context. -/
def removeAssignment (mv : MVarId) : MetaM Unit := do
  -- remove the assignment
  let mctx ← getMCtx
  let mctxassgn := mctx.eAssignment.erase mv
  setMCtx {mctx with eAssignment := mctxassgn} -- mctxassgn

/-- Instantiates all mvars in e except the mvar given by the array a -/
def instantiateMVarsExcept (a : Array MVarId) (e : Expr)  : MetaM Expr := do
  for mv in a do
   removeAssignment mv -- remove the assignment
  let e ← instantiateMVars e -- instantiate mvars
  return e

/-- Getting theorem statement from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.type -- return the theorem statement

/-- Get a hypothesis by its name -/
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
      then return ← instantiateMVars hyp.value
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

/-- Get (in a list) all subexpressions in an expression -/
partial def getSubexpressionsIn (e : Expr) : MetaM (List Expr) := do
  let rec getSubexpressionsInRec (e : Expr) (acc : List Expr) : MetaM (List Expr) :=
    match e with
    | Expr.forallE n d b bi   => do
                                  let d_subexprs ← getSubexpressionsInRec d acc
                                  withLocalDecl n bi d (fun placeholder => do
                                    let b := b.instantiate1 placeholder
                                    let b_subexprs ← getSubexpressionsInRec b acc -- now it's safe to recurse on b (no loose bvars)
                                    let b_subexprs ← b_subexprs.mapM (fun s => mkForallFVars #[placeholder] s (binderInfoForMVars := bi)) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                                    return [e] ++ d_subexprs ++ b_subexprs
                                  )
    | Expr.lam n d b bi       => do
                                  let d_subexprs ← getSubexpressionsInRec d acc
                                  withLocalDecl n bi d (fun placeholder => do
                                    let b := b.instantiate1 placeholder
                                    let b_subexprs ← getSubexpressionsInRec b acc -- now it's safe to recurse on b (no loose bvars)
                                    let b_subexprs ← b_subexprs.mapM (fun s => mkLambdaFVars #[placeholder] s (binderInfoForMVars := bi))
                                    return [e] ++ d_subexprs ++ b_subexprs
                                  )
 -- | Expr.letE _ t v b _    => [e] ++ (← getSubexpressionsInRec t acc) ++ (← getSubexpressionsInRec v acc) ++ (← getSubexpressionsInRec b acc)
    | Expr.app f a           => return [e] ++ (← getSubexpressionsInRec f acc) ++ (← getSubexpressionsInRec a acc)
    | Expr.mdata _ b         => return [e] ++ (← getSubexpressionsInRec b acc)
    | Expr.proj _ _ b        => return [e] ++ (← getSubexpressionsInRec b acc)
    | Expr.mvar _            => return [e] ++ acc
    | Expr.bvar _            => return [e] ++ acc
    | _                      => return [e] ++ acc
  let subexprs ← (getSubexpressionsInRec e [])
  --logInfo m!"subexprs before bvar filter {subexprs}"
  let subexprs := subexprs.filter $ fun subexpr => !subexpr.hasLooseBVars -- remove the ones that will cause errors when parsing
  return subexprs

/-- Returns true if "e" contains "subexpr".  Differs from "occurs" because this uses the coarser "isDefEq" rather than "==" -/
def containsExpr(subexpr : Expr)  (e : Expr) : MetaM Bool := do
  let e_subexprs ← getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => withoutModifyingState (isDefEq e_subexpr subexpr))
  return firstExprContainingSubexpr.isSome

/-- Replaces all subexpressions where "condition" holds with the "replacement" in the expression e -/
def containsExprWhere (condition : Expr → Bool) (e : Expr)   : MetaM Bool := do
  let e_subexprs ← getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return condition e_subexpr)
  return firstExprContainingSubexpr.isSome

/-- Returns true if the expression contains metadata -/
def containsMData (e : Expr): MetaM Bool := do
  return ← containsExprWhere (Expr.isMData) e

/-- Returns the assignment of metavariable `m` -/
def getAssignmentFor (m : MVarId) : MetaM (Option Expr) := do
  let e ← getExprMVarAssignment? m
  return e

/-- Returns true if the expression is assigned to another expression containing metadata -/
def assignmentContainsMData (m : MVarId) : MetaM Bool := do
  let m_assignment ← getAssignmentFor m
  if (m_assignment.isSome) then
    if (← containsMData (← m_assignment)) then
      return True
  return False

/-- Returns a list of all metavariables whose assignment contains metadata -/
def getAllMVarsContainingMData (a : Array MVarId): MetaM (Array MVarId) :=
   a.filterM assignmentContainsMData

/-- Turn a lemma name into its generalized version by prefixing it with `gen_` and truncating. -/
def mkAbstractedName (n : Name) : Name :=
    match n with
    | (.str _ s) =>  Name.mkSimple s!"gen_{s.takeWhile (fun c => c != '_')}" -- (fun c => c.isLower && c != '_')
    | _ => `unknown

/-- Returns true if given an expression `e` has a metavariable of type `t`-/
def hasMVarOfType (t e: Expr) : MetaM Bool := do
  let mvarIds ← getMVars e
  mvarIds.anyM (fun m => do withoutModifyingState (isDefEq (← m.getType') t))

/- Replaces all instances of "p" in "e" with a metavariable.
Roughly implemented like kabstract, with the following differences:
  kabstract replaces "p" with a bvar, while this replaces "p" with an mvar
  kabstract replaces "p" with the same bvar, while this replaces each instance with a different mvar
  kabstract doesn't look for instances of "p" in the types of constants, this does
  kabstract doesn't look under loose bvars, but this creates localdecls so we can still look under bvars
-/
-- NOTE (future TODO): this code can now be rewritten without `withLocalDecl` or `mkFreshExprMVarAt`
partial def replacePatternWithMVars (e : Expr) (p : Expr) : MetaM Expr := do
  -- return e
  let (lctx, linst) := (← getLCtx, ← getLocalInstances)
  let pType ← inferType p

  --return e
  -- the "depth" here is not depth of expression, but how many constants / theorems / inference rules we have unfolded
  let rec visit (e : Expr) (depth : ℕ := 0): MetaM Expr := do

    -- let e ← whnf e
    -- logInfo m!"recursing on {e} with constructor {e.ctorName}"
    let visitChildren : Unit → MetaM Expr := fun _ => do
      if e.hasLooseBVars then
        logInfo m!"Loose BVars detected on expression {e}"
      match e with
      -- unify types of metavariables as soon as we get a chance in .app
      -- that is, ensure that fAbs and aAbs are in sync about their metavariables
      | .app f a         => --logInfo m!"recursing under function {f} of type {← inferType f}"
                            let fAbs ← visit f depth
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
                                -- logInfo m!"lamda body: {b}"
                                let bAbs ←
                                  if (← withoutModifyingState (isDefEq dAbs d)) then
                                    visit b depth-- now it's safe to recurse on b (no loose bvars)
                                  else
                                    logInfo m!"dAbs {dAbs} and d {d} are not defeq"
                                    return b
                                return ← mkLambdaFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                              )
                              if updatedLambda.hasLooseBVars then
                                logInfo m!"Loose BVars detected on expression {e}"
                              return updatedLambda
      | .forallE n d b bi => --logInfo m!"Recursing under forall {d}"
                              let dAbs ← visit d depth
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
      | .const n _       => let constType ← getTheoremStatement n
                            -- logInfo m!"const type {constType}"
                            if depth ≥ 10 then return e
                            else
                                -- if (← containsExpr p constType) then
                                let genConstType ← visit constType (depth+1)  -- expr for generalized proof statment
                                -- if the const does have the pattern in its definition, it is a property we should generalize
                                if ← hasMVarOfType pType genConstType then
                                  logInfo m!"has gen const type {genConstType}"
                                  let m ← mkFreshExprMVarAt lctx linst genConstType (kind := .synthetic) (userName := mkAbstractedName n)-- mvar for generalized proof
                                  -- let m ← mkFreshExprMVar genConstType -- mvar for generalized proof
                                  return m

                                -- otherwise, we don't need to expand the definition of the const
                                else return e
      | e                => --logInfo m!"Can't recurse under this expression \n {e}"
                            return e

    if e.hasLooseBVars then
      logInfo "Loose BVars detected"
      visitChildren ()
    else
      -- if the expression "e" is the pattern you want to replace...
      let mctx ← getMCtx
      if ← (isDefEq e p) then
        let m ← mkFreshExprMVarAt lctx linst pType --(userName := `n) -- replace every occurrence of pattern with mvar
        -- let m ← mkFreshExprMVar pType -- replace every occurrence of pattern with mvar
        return m
      -- otherwise, "e" might contain the pattern...
      else
        setMCtx mctx
        -- so that other matches are still possible.
        visitChildren ()
  visit e

/- Just like kabstract, except abstracts to mvars instead of bvars -/
def abstractToOneMVar (thmType : Expr) (pattern : Expr) (occs : Occurrences) : MetaM Expr := do
  let userThmType ← kabstract thmType pattern (occs)

  let userMVar ←  mkFreshExprMVar (← inferType pattern)
  let annotatedMVar := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ userMVar
  let userThmType := userThmType.instantiate1 annotatedMVar

  return userThmType

/- Just like kabstract, except abstracts to different variables instead of the same one -/
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

/-- Make all mvars in mvarArray with the type t the same  -/
def setEqualAllMVarsOfType (mvarArray : Array MVarId) (t : Expr) : MetaM Unit := do
  let m ← mkFreshExprMVar t -- new mvar to replace all others with the same type
  for mv in mvarArray do
    if ← isDefEq (← mv.getType) t then
      if !(← mv.isAssigned) then mv.assignIfDefeq m

/-- Pull out mvars as hypotheses to create a chained implication-/
def pullOutMissingHolesAsHypotheses (proof : Expr) : MetaM Expr :=
  return (← abstractMVars proof).expr

/-- Unifies metavariables (which are hypotheses) when possible.  -/
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

/-- Re-specialize the occurrences of the pattern we are not interested in -/
def respecializeOccurrences (thmType : Expr) (genThmProof : Expr) (pattern : Expr) (occsToStayAbstracted : Occurrences) (consolidate : Bool) : MetaM Expr := do
  -- Get the occurrences of the pattern (in the theorem statement) the user wants to specialize
  let userThmType ← if consolidate then
    abstractToOneMVar thmType pattern occsToStayAbstracted
  else
    abstractToDiffMVars thmType pattern occsToStayAbstracted
  logInfo m!"!User Generalized Type: {userThmType}"

  -- Keep a record of mvars to keep track of
  let genThmType ← inferType genThmProof
  let mvarsInProof := (← getMVars genThmProof) ++ (← getMVars genThmType)

  -- Compare and unify mvars between user type and our generalized type
  let _ ← isDefEq  genThmType userThmType

  -- Instantiate the ones we don't want to generalize
  let userSelectedMVars ← getAllMVarsContainingMData mvarsInProof
  return ← instantiateMVarsExcept userSelectedMVars genThmProof

/-- Run Lean's built-in "simp" tactic -/
def performSimp (genThmType : Expr ) (genThmProof : Expr ): MetaM (Expr × Expr) := do
  let (result, _) ← Lean.Meta.simp genThmType {}
  let genThmTypeSimp := result.expr
  let genThmProofSimp ← mkAppM `Eq.mpr #[← result.getProof, genThmProof]
  return (genThmTypeSimp, genThmProofSimp)

/-- Instantiate metavariables according to what unifies in a typecheck -/
def consolidateWithTypecheck (proof : Expr) : MetaM Expr := do
  try
    check proof
  catch e =>
    throwError "The type of the proof doesn't match the statement.  Perhaps a computation rule was used?"
  return ← instantiateMVars proof

/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (pattern : Expr) (occs : Occurrences := .all) (consolidate : Bool := false) : TacticM Unit := withMainContext do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) := (← getHypothesisType thmName, ← getHypothesisProof thmName)
  logInfo m!"!Tactic Initial Proof: { thmProof}"
  -- logInfo m!"!Tactic Initial Type: { ← inferType thmProof}"


  -- logInfo m!"the initial thm has mvars? {← getMVars thmType}"
  -- Get the generalized theorem (replace instances of pattern with mvars, and unify mvars where possible)
  let mut genThmProof := thmProof
  genThmProof ← replacePatternWithMVars genThmProof pattern -- replace instances of f's old value with metavariables
  logInfo m!"!Tactic Generalized Proof After Abstraction: { genThmProof}"

  -- Consolidate mvars within proof term by running a typecheck
  genThmProof ← consolidateWithTypecheck genThmProof
  logInfo m!"!Tactic Generalized Proof After Typecheck: { genThmProof}"

  let genThmType ← inferType genThmProof

  -- Re-specialize the occurrences of the pattern we are not interested in
  if !(occs == .all) then do
    genThmProof ← respecializeOccurrences thmType genThmProof pattern (occsToStayAbstracted := occs) consolidate
    logInfo m!"!Tactic Generalized Type After Unifying: {← inferType genThmProof}"

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
  genThmProof ←  pullOutMissingHolesAsHypotheses genThmProof --logInfo ("Tactic Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; --logInfo ("Tactic Generalized Type: " ++ genThmType)

  -- Run "simp".
  -- let (genThmType, genThmProof) ← performSimp genThmType genThmProof

  -- Add the generalized theorem to the context.
  createLetHypothesis genThmType genThmProof (thmName++`Gen)

  logInfo s!"Successfully generalized \n  {thmName} \nto \n  {thmName++`Gen} \nby abstracting {← ppExpr pattern}."


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Autogeneralizes the "pattern" in the hypothesis "h",
But generalizes all occurrences in the same way.  Behaves as in (Pons, 2000)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- A tactic that generalizes all instances of `pattern` in a local hypotheses `h` by requiring `pattern` to have only the properties used in the proof of `h`. Behaves as in ("Generalization in Type Theory Based Proof Assistants" by Olivier Pons, 2000).-/
elab "autogeneralize_basic" pattern:term "in" h:ident : tactic => do
  let pattern ← (Lean.Elab.Term.elabTerm pattern none)
  let h := h.getId
  autogeneralize h pattern (occs:=.all) (consolidate:=true)

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Autogeneralizes the "pattern" in the hypothesis "h",
Default behavior is to generalizes all occurrences separately, but can generalize at specified occurences.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
/- Parse occurrences of the term as specified by the user.-/
syntax occurrences :="at" "occurrences" "[" num+ "]"
def decodeOccurrences : TSyntax `Autogeneralize.occurrences → List Nat
  | `(occurrences| at occurrences [$occs*]) => (occs.map TSyntax.getNat).toList
  | _ => unreachable!

/-- A tactic that generalizes all instances of `pattern` in a local hypotheses `h` by requiring `pattern` to have only the properties used in the proof of `h`.-/
elab "autogeneralize" pattern:term "in" h:ident occs:(Autogeneralize.occurrences)? : tactic => do
  let pattern ← (Lean.Elab.Term.elabTerm pattern none)
  let h := h.getId
  let occs := occs.map decodeOccurrences
  if occs.isSome then
    autogeneralize h pattern (Occurrences.pos $ ← occs)
  else
    autogeneralize h pattern -- generalize all occurrences (default: to different mvars)

end Autogeneralize
