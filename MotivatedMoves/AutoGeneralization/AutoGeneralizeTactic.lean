import Lean
import MotivatedMoves.AutoGeneralization.Helpers.ReplaceWithMVars

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize


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


/-- Instantiate metavariables according to what unifies in a typecheck -/
def consolidateWithTypecheck (proof : Expr) : MetaM Expr := do
  try
    check proof
  catch e =>
    logInfo m!"Error: {e.toMessageData}"
    throwError "The type of the proof doesn't match the statement.  Perhaps a computation rule was used?"
  return ← instantiateMVars proof


/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (pattern : Expr) (occs : Occurrences := .all) (consolidate : Bool := false) : TacticM Unit := withMainContext do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) ← getTheoremAndProof thmName
  logInfo m!"!Tactic Initial Proof: { thmProof}"

  -- Get the generalized theorem (replace instances of pattern with mvars, and unify mvars where possible)
  let mut genThmProof := thmProof
  let mut changes := []
  (genThmProof, changes) ← replacePatternWithMVars genThmProof pattern (← getLCtx) (← getLocalInstances) (detectConflicts? := true)  |>.run [] -- replace instances of f's old value with metavariables
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

  -- Give the meta-variables in the proof more human-readable names
  relabelMVarsIn genThmProof

  -- Remove repeating hypotheses
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
