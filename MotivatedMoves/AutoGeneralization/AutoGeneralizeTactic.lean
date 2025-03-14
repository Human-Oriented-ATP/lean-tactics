import Lean
import MotivatedMoves.AutoGeneralization.Helpers.GoalsAndHypotheses
import MotivatedMoves.AutoGeneralization.Helpers.ReplacePatternWithMVars
import MotivatedMoves.AutoGeneralization.Helpers.Simplification
import MotivatedMoves.AutoGeneralization.Helpers.Unification

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize

initialize
  registerTraceClass `ProofPrinting

/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (pattern : Expr) (occs : Occurrences := .all) (consolidate : Bool := false) : TacticM Unit := withMainContext do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) ← getTheoremAndProof thmName
  trace[ProofPrinting] m!"!Tactic Initial Proof: { thmProof}"

  -- Get the generalized theorem (replace instances of pattern with mvars)
  let mut genThmProof := thmProof
  let mut dependenciesToGeneralize := [] -- keep track of dependencies of what must be generalized first
  (_, dependenciesToGeneralize) ← replacePatternWithMVars genThmProof pattern (← getLCtx) (← getLocalInstances) (detectConflicts? := true)  |>.run [] -- replace instances of f's old value with metavariables
  trace[ProofPrinting] m!"!Tactic Generalized Proof After Abstraction: { genThmProof}"

  -- Generalize all constants that `pattern` has dependencies on, and then generalize `pattern`
  dependenciesToGeneralize := dependenciesToGeneralize.eraseDups ++ [pattern]
  logInfo m!"ALL DEPENDENCIES: {dependenciesToGeneralize}"
  for dep in dependenciesToGeneralize do
    genThmProof ← replacePatternWithMVars genThmProof dep (← getLCtx) (← getLocalInstances) (detectConflicts? := false) |>.run' []

  trace[ProofPrinting] m!"!Tactic Generalized Proof After Abstraction: { genThmProof}"

  logInfo m!"ALL DEPENDENCIES: {dependenciesToGeneralize}"
  -- Generalize all the actual `pattern`

  -- Consolidate mvars within proof term by running a typecheck
  genThmProof ← consolidateWithTypecheck genThmProof
  trace[ProofPrinting] m!"!Tactic Generalized Proof After Typecheck: { genThmProof}"
  let genThmType ← inferType genThmProof

  -- Re-specialize the occurrences of the pattern we are not interested in
  if !(occs == .all) then do
    genThmProof ← respecializeOccurrences thmType genThmProof pattern (occsToStayAbstracted := occs) consolidate
    trace[ProofPrinting] m!"!Tactic Generalized Type After Unifying: {← inferType genThmProof}"

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
