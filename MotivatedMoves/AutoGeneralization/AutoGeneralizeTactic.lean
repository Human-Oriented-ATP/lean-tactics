import Lean
import Qq
import MotivatedMoves.AutoGeneralization.Antiunification
import MotivatedMoves.AutoGeneralization.Helpers

open Lean Elab Tactic Meta Term Command AntiUnify

namespace Autogeneralize

def placeholderName := `placeholder
def preferredNames := #[`n, `m, `p, `a, `b, `c]

/-- Turn a lemma name into its generalized version by prefixing it with `gen_` and truncating. -/
def mkAbstractedName (n : Name) : Name :=
    match n with
    | (.str _ s) =>  Name.mkSimple s!"gen_{s.takeWhile (fun c => c != '_')}" -- (fun c => c.isLower && c != '_')
    | _ => `unknown


def getTermsToGeneralize (e e' : Expr) : MetaM (List Expr) := do
  let mismatches ← getMismatches e e'
  return ← mismatches.filterMapM fun ⟨_, left, right⟩ ↦ do
    let l ← getMVars left
    let r ← getMVars right
    if l.size < r.size then
      return left
    else if r.size < l.size then
      return right
    else
      return none

/-- Returns the argument to an expression e.g. if fAbs has type "n-1= 3 → n=4" then it returns "n-1=3"-/
def extractArgType (fAbs : Expr) : MetaM Expr := do
  let fAbsType ← inferType fAbs
  return fAbsType.bindingDomain!

/- Replaces all instances of "p" in "e" with a metavariable.
Roughly implemented like kabstract, with the following differences:
  kabstract replaces "p" with a bvar, while this replaces "p" with an mvar
  kabstract replaces "p" with the same bvar, while this replaces each instance with a different mvar
  kabstract doesn't look for instances of "p" in the types of constants, this does
  kabstract doesn't look under loose bvars, but this creates localdecls so we can still look under bvars
-/

-- NOTE (future TODO): this code can now be rewritten without `withLocalDecl` or `mkFreshExprMVarAt`
partial def replacePatternWithMVars (e : Expr) (p : Expr) (lctx : LocalContext) (linsts : LocalInstances) (detectConflicts? := false) : StateT (List Expr) MetaM Expr := do
  -- return e
  logInfo m!"We are replacing the pattern {p}:{← inferType p} with mvars."
  -- abstracting `p` so that it can be transported to other meta-variable contexts
  let pAbs ← abstractMVars p (levels := false) -- the `(levels := false)` prevents bizarre instantiations across universe levels

  -- let _ ← abstractIfTypeContainsP e p

  -- the "depth" here is not depth of expression, but how many constants / theorems / inference rules we have unfolded
  let rec visit (e : Expr) (depth : Nat := 0): StateT (List Expr) MetaM Expr := do

    let visitChildren : Unit →  StateT (List Expr) MetaM Expr := fun _ => do
      if e.hasLooseBVars then
        logInfo m!"Loose BVars detected on expression {e}"
      match e with
      -- unify types of metavariables as soon as we get a chance in .app
      -- that is, ensure that fAbs and aAbs are in sync about their metavariables
| .app f a         => --logInfo m!"recursing under function {f} of type {← inferType f}"
                          if detectConflicts? then
                            let mut fAbs ← visit f depth -- the type
                            let mut aAbs ← visit a depth -- the term
                            try
                              check $ .app fAbs aAbs
                              return e.updateApp! fAbs aAbs
                            catch err =>  -- as an argument to fabs, feed in an mvar with the type it is expected to have.
                              let expectedA ← extractArgType fAbs
                              logInfo m!"Error in typechecking: {err.toMessageData}"
                              logInfo m!"aAbs was expected to have type \n\t{← instantiateMVars expectedA} \nbut has type \n\t{← instantiateMVars =<< inferType aAbs}"

                              -- the mismatch is probably caused because something else needs to be generalized
                              let problemTerms ← getTermsToGeneralize expectedA (← inferType aAbs)
                              logInfo m!"The mismatch can probably be fixed by generalizing the terms {problemTerms}"
                              modify (problemTerms ++ ·)

                              -- for t in problemTerms do
                              --   fAbs ← replacePatternWithMVars fAbs t lctx linsts (detectConflicts? := detectConflicts?)
                              --   aAbs ← replacePatternWithMVars aAbs t lctx linsts (detectConflicts? := detectConflicts?)

                              return e.updateApp! fAbs aAbs
                              -- if this doesn't typecheck, that means probably that term has been generalized,
                              -- but type still has the pattern (or a comp rule was used).
                              -- so to fix it, we should discard the proof entirely (by making it a mvar
                          else
                            let fAbs ← visit f depth
                            let aAbs ← visit a depth
                            return e.updateApp! fAbs aAbs

      | .mdata _ b       => return e.updateMData! (← visit b depth)
      | .proj _ _ b      => return e.updateProj! (← visit b depth)
      | .letE n t v b _ =>  let tAbs ← visit t depth
                            let vAbs ← visit v depth
                            -- this consolidates the metavariables in the generalized type and the generalized value
                            -- isDefEq tAbs (← inferType vAbs)
                            -- let updatedLetBody ← withLocalDecl n .implicit tAbs (fun placeholder => do
                            let updatedLet ← withLetDecl n tAbs vAbs (fun placeholder => do
                              let b := b.instantiate1 placeholder
                              let bAbs ← if (←  liftM <| withoutModifyingState (isDefEq tAbs t)) then
                                    visit b depth -- now it's safe to recurse on b (no loose bvars)
                                  else
                                    logInfo m!"tAbs {tAbs} and t {t} are not defeq"
                                    return b
                              return ← mkLetFVars #[placeholder] bAbs-- put the "n:tAbs" back in the expression itself instead of in an external fvar
                            )
                            return updatedLet
      | .lam n d b bi     =>
                              let dAbs ← visit d depth
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedLambda ← withLocalDecl n bi dAbs (fun placeholder => do
                                let b := b.instantiate1 placeholder
                                -- logInfo m!"lamda body: {b}"
                                let bAbs ←
                                  if (←  liftM <| withoutModifyingState (isDefEq dAbs d)) then
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
      | .const n us      => let constType ← inferType (.const n us) -- this ensures that univverse levels are instantiated correctly
                            -- logInfo m!"name {n}"
                            -- if marked as a theorem not to explore, do not recurse
                            if n.toString.endsWith "_opaque" then
                              logInfo m!"!!!HERE IS THE MATCH!! WILL NOT RECURSE"
                              -- return e
                            if depth ≥ 2 then return e
                            else
                                -- if (← containsExpr p constType) then
                                let genConstType ← visit constType (depth+1)  -- expr for generalized proof statment
                                -- if the const does have the pattern in its definition, it is a property we should generalize
                                -- it may be safer to just check whether the generalized type has any meta-variables at all,
                                -- rather than looking for ones of a specific type, since there's a chance of false negatives with the latter
                                if genConstType.hasExprMVar then
                                  let m ← mkFreshExprMVarAt lctx linsts genConstType (kind := .synthetic) (userName := mkAbstractedName n)-- mvar for generalized proof
                                  -- logInfo m!"made mvar {m} of type {genConstType}"
                                  return m

                                -- otherwise, we don't need to expand the definition of the const
                                else return e
      | e                => --logInfo m!"Can't recurse under this expression \n {e}"
                            return e

    if e.hasLooseBVars then
      logInfo "Loose BVars detected, so we visit children."
      visitChildren ()
    else
      -- if the expression "e" is the pattern you want to replace...
      let mctx ← getMCtx
      let (_, _, p) ← openAbstractMVarsResult pAbs
      if !e.isMVar && (←  liftM <|  withoutModifyingState (isDefEq e p)) then
        -- since the type of `p` may be slightly different each time depending on the context it's in, we infer its type each time
        let m ← mkFreshExprMVarAt lctx linsts (← inferType p) (userName := placeholderName) --(kind := .syntheticOpaque) -- replace every occurrence of pattern with mvar
        -- let m ← mkFreshExprMVar (← inferType p) (userName := `n) -- replace every occurrence of pattern with mvar
        -- let m ← mkFreshExprMVar pType -- replace every occurrence of pattern with mvar
        -- logInfo m!"made mvar {m} of type {pType}"
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
      if !(← mv.isAssigned) then mv.assign m--mv.assignIfDefeq m

/-- Relabel the metavariables in the expression with their preferred names. -/
def relabelMVarsIn (e : Expr) : MetaM Unit := do
  let mvars ← getMVars e
  let placeholderMVars ← mvars.filterM fun mvar => do
   return (← mvar.getTag).getRoot.toString.startsWith placeholderName.toString
  for (mvar, name) in placeholderMVars.zip preferredNames do
      mvar.setUserName name

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
      -- else if (hyp₁.name.toString.startsWith "inst" ∧ hyp₂.name.toString.startsWith "inst") then do
      --   discard <| isDefEq (.mvar hyp₁) (.mvar hyp₂)

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

-- Our custom typechecking function (based on Lean's check)
-- But in case of error, just replaces a type with its expected type.
-- def check (e : Expr) : MetaM Unit :=
--   withTraceNode `Meta.check (fun res =>
--       return m!"{if res.isOk then checkEmoji else crossEmoji} {e}") do
--     try
--       withTransparency TransparencyMode.all $ checkAux e
--     catch ex =>
--       trace[Meta.check] ex.toMessageData
--       throw ex


/-- Instantiate metavariables according to what unifies in a typecheck -/
def consolidateWithTypecheck (proof : Expr) : MetaM Expr := do
  try
    check proof
  catch e =>
    logInfo m!"Error: {e.toMessageData}"
    throwError "The type of the proof doesn't match the statement.  Perhaps a computation rule was used?"
  return ← instantiateMVars proof

/-- Get the specifying theorem from a local hypothesis if that exists, and otherwise from the environment -/
def getTheoremAndProof (thmName : Name) : TacticM (Expr × Expr) := do
  try return (← getHypothesisType thmName, ← getHypothesisProof thmName) -- if the theorem is a hypothesis of the current proof state
  catch _ => return (← getTheoremStatement thmName, ← getTheoremProof thmName) -- if the theorem is in the environment

/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (pattern : Expr) (occs : Occurrences := .all) (consolidate : Bool := false) : TacticM Unit := withMainContext do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) ← getTheoremAndProof thmName
  logInfo m!"!Tactic Initial Proof: { thmProof}"
  -- logInfo m!"!Tactic Initial Type: { ← inferType thmProof}"


  -- logInfo m!"the initial thm has mvars? {← getMVars thmType}"
  -- Get the generalized theorem (replace instances of pattern with mvars, and unify mvars where possible)
  let mut genThmProof := thmProof
  let mut changes := []
  (genThmProof, changes) ← replacePatternWithMVars genThmProof pattern (← getLCtx) (← getLocalInstances) (detectConflicts? := true)  |>.run [] -- replace instances of f's old value with metavariables
  -- genThmProof ← replacePatternWithMVars genThmProof pattern (← getLCtx) (← getLocalInstances) |>.run' [] -- replace instances of f's old value with metavariables
  logInfo m!"!Tactic Generalized Proof After Abstraction: { genThmProof}"

  changes := changes.eraseDups
  for change in changes do
    logInfo m!"Change: {change}"
    genThmProof ← replacePatternWithMVars genThmProof change (← getLCtx) (← getLocalInstances) (detectConflicts? := false) |>.run' []

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

  -- this gives the meta-variables in the proof more human-readable names
  relabelMVarsIn genThmProof

  -- Remove repeating hypotheses.
  genThmProof ← removeRepeatingHypotheses genThmProof

  -- Pull out the holes (the abstracted term & all hypotheses on it) into a chained implication.
  genThmProof ←  pullOutMissingHolesAsHypotheses genThmProof --logInfo ("Tactic Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; --logInfo ("Tactic Generalized Type: " ++ genThmType)

  -- Run "simp".
  -- let (simpgenThmType, simpgenThmProof) ← performSimp genThmType genThmProof

  -- Add the generalized theorem to the context.
  createLetHypothesis genThmType genThmProof (thmName++`Gen)
  -- createLetHypothesis simpgenThmType simpgenThmProof (thmName++`Gen)

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
  match occs with
  | some occsList => autogeneralize h pattern (Occurrences.pos occsList)
  | none => autogeneralize h pattern -- generalize all occurrences (default: to different mvars)

end Autogeneralize
