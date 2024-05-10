import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/
import Mathlib.Data.Real.Irrational

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize

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

/-- Get the FVarID for a hypothesis (given its name) -/
def getHypothesisFVarId (h : Name) : TacticM FVarId := do
  let hyp ← getHypothesisByName h
  return hyp.fvarId

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
          else return hyp.value -- works if proved directly with a proof term like `:= fun ...`
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

/-- Getting theorems from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | throwError ("Could not find a theorem with name " ++ n) -- get the declaration with that name
  return thm.type -- return the theorem statement (the type is the proposition)

#eval do {let e ← getTheoremStatement ``multPermute; logExpression e}

#eval getTheoremStatement ``multPermute
#eval do {let e ← getTheoremStatement ``multPermute; logPrettyExpression e}

#eval do {let e ← getTheoremStatement ``multPermute; logFormattedExpression e}
#eval do {let e ← getTheoremStatement ``multPermute; logExpressionType e}

/-- Getting theorem proof from context --/
def getTheoremProof (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | failure -- get the declaration with that name
  return thm.value! -- return the theorem proof (the term is the proof)

#eval do {let e ← getTheoremProof ``reflOfZero; logExpression e}
#eval do {let e ← getTheoremProof ``reflOfZero; logFormattedExpression e}
#eval do {let e ← getTheoremProof ``reflOfZero; logPrettyExpression e}

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

/-- Generalizing a term in a theorem  -/
def generalizeTerm (e : Expr) (x? : Option Name := none) (h? : Option Name := none) : TacticM Unit := do
    let x := x?.getD (← mkPrettyName `x 0) -- use the given variable name, or if it's not there, make one
    let h := h?.getD (← mkPrettyName `h 0) -- use the given hypothesis name, or if it's not there, make one
    let genArg : GeneralizeArg := { expr := e, xName? := x, hName? := h }
    let (_, new_goal) ← (←getGoalVar).generalize (List.toArray [genArg])
    setGoals [new_goal]

/-- Generalizing a term in a theorem, then returning the name and type of the new generalized variable-/
def generalizeTerm' (e : Expr) (x? : Option Name := none) (h? : Option Name := none) : TacticM (Name × Expr) := do
    let x := x?.getD (← mkPrettyName `x 0) -- use the given variable name, or if it's not there, make one
    let h := h?.getD (← mkPrettyName `h 0) -- use the given hypothesis name, or if it's not there, make one
    let genArg : GeneralizeArg := { expr := e, xName? := x, hName? := h }
    let (_, new_goal) ← (←getGoalVar).generalize (List.toArray [genArg])
    setGoals [new_goal]

    return (x, ← getHypothesisType x) -- name and type of new generalized variable


/-- Generalizing a term in the hypothesis, then returning the name and type of the new generalized variable-/
def generalizeTermInHypothesis (hypToGeneralize : FVarId) (e : Expr) (x? : Option Name := none) (h? : Option Name := none) : TacticM (Name × Expr × FVarId) := do
    let x := x?.getD (← mkPrettyName `x 0) -- use the given variable name, or if it's not there, make one
    let genArg : GeneralizeArg := { expr := e, xName? := x}

    let goal ← getGoalVar
    goal.withContext do
      let (_, _, new_goal) ← goal.generalizeHyp [genArg].toArray  [hypToGeneralize].toArray
      setGoals [new_goal]

    return (x, ← getHypothesisType x, ← getHypothesisFVarId x) -- name and type of new generalized variable



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

/-- Gets all identifier names in an expression -/
def getFreeIdentifiers (e : Expr) : List Name := e.getUsedConstants.toList

-- TO DO: use traverseExpr to do this instead
/-- Creating replaces "original" with "replacement" in an expression -- as long as the subexpression found is definitionally equal to "original" -/
def replaceCoarsely (original : Expr) (replacement: Expr) : Expr → MetaM Expr := fun e => do
  -- if there's a loose bvar in the expression, don't try checking definitional equality
  if !e.hasLooseBVars then
    if (← isDefEq e original)  -- do the replacement if you find a match
      then return replacement
    else match e with -- otherwise recurse to find more matches
    | Expr.forallE n d b bi  => return Expr.forallE n (← replaceCoarsely original replacement d) (← replaceCoarsely original replacement b) bi
    | Expr.lam n d b bi      => return Expr.lam n (← replaceCoarsely original replacement d) (← replaceCoarsely original replacement b) bi
    | Expr.app f a           => return Expr.app (← replaceCoarsely original replacement f) (← replaceCoarsely original replacement a)
    | Expr.letE n t v b x    => return Expr.letE n (← replaceCoarsely original replacement t) (← replaceCoarsely original replacement v) (← replaceCoarsely original replacement b) x
    | misc                     => return misc -- no need to recurse on any of the other expressions...if they didn't match "original" already, they won't if you go any deeper.
  else match e with -- otherwise recurse to find more matches
  | Expr.forallE n d b bi  => return Expr.forallE n (← replaceCoarsely original replacement d) (← replaceCoarsely original replacement b) bi
  | Expr.lam n d b bi      => return Expr.lam n (← replaceCoarsely original replacement d) (← replaceCoarsely original replacement b) bi
  | Expr.app f a           => return Expr.app (← replaceCoarsely original replacement f) (← replaceCoarsely original replacement a)
  | Expr.letE n t v b x    => return Expr.letE n (← replaceCoarsely original replacement t) (← replaceCoarsely original replacement v) (← replaceCoarsely original replacement b) x
  | misc                     => return misc -- no need to recurse on any of the other expressions...if they didn't match "original" already, they won't if you go any deeper.

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

/-- Replaces every occurence in e of old[0] with new[0], and old[1] with new[1] and so on -/
def replaceAll (original : List Name) (replacement : List Name) (e : Expr): MetaM Expr := do
  let dict : HashMap Name Name := HashMap.ofList (original.zip replacement)
  match e with
  | .const n []       =>  if original.contains n then return (.const (← dict[n]) []) else return (.const n [])
  | .forallE n d b bi  => return .forallE n (← replaceAll original replacement d) (← replaceAll original replacement b) bi
  | .lam n d b bi      => return .lam n (← replaceAll original replacement d) (← replaceAll original replacement b) bi
  | .app f a           => return .app (← replaceAll original replacement f) (← replaceAll original replacement a)
  | .letE n t v b x    => return .letE n (← replaceAll original replacement t) (← replaceAll original replacement v) (← replaceAll original replacement b) x
  | misc               => return misc -- no need to recurse on any of the other expressions...if they didn't match "original" already, they won't if you go any deeper.

/-- Replaces every occurence in e of the name "original" with the name "replacement" -/
def replace (original :  Name) (replacement : Name) (e : Expr): MetaM Expr := do
  replaceAll [original] [replacement] e

/-- Replaces every occurence in e of the name "original" with the name of the FVar "replacementFVar" -/
def replaceWithFVar (original :  Name) (replacementFVar : Expr) (e : Expr): MetaM Expr := do
  let replacement := replacementFVar.fvarId!.name
  replace original replacement e

/-
Replaces all instances of an expression with the outermost bound variable (to help build a lambda or for-all)
Do this to the expression BEFORE wrapping it in a lambda or for-all.
-/
def replaceWithBVar (original : Expr) (e : Expr) (depth : Nat := 0) : MetaM Expr :=
  match e with
    | .lam n a b bi => return .lam n (← replaceWithBVar original a (depth)) (← replaceWithBVar original b (depth+1)) bi
    | .forallE n a b bi => return .forallE n (← replaceWithBVar original a (depth)) (← replaceWithBVar original b (depth+1)) bi
    | x =>  replaceCoarsely (original) (.bvar depth) x

/-- Returns true if "e" contains "subexpr".  Differs from "occurs" because this uses the coarser "isDefEq" rather than "==" -/
def containsExpr(subexpr : Expr)  (e : Expr) : MetaM Bool := do
  let e_subexprs := getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return ← isDefEq e_subexpr subexpr)
  return firstExprContainingSubexpr.isSome

/--This is the term that we are generalizing to an arbitrary term of that type -/
structure GeneralizedTerm where
  oldValue : Expr                 -- e.g. Hmul.hmul
  name : Name         := `f       -- e.g. f
  type : Expr                     -- e.g. ℕ → ℕ → ℕ
  placeholder : Expr              -- e.g. .mvar #2383...to uniquely identify where it is
deriving Repr

/--These are the properties the generalized term needs to adhere to in order for the proof to still hold -/
structure Modifier where
  oldName : Name                    -- name that exists in the context e.g. Nat.mul_assoc
  newName : Name := mkAbstractedName oldName -- usually something like gen_mul_assoc
  oldType : Expr                    -- the type that has the ungeneralized "f"
  newType : Expr                    -- the type that has the placeholder of "f"
deriving Inhabited

def makeModifiers (oldNames : List Name) (oldTypes: List Expr) (newTypes: List Expr) : Array Modifier :=
  let modifiers : Array Modifier := oldNames.length.fold (fun i (modifiers : Array Modifier) =>
    let modifier : Modifier := {
      oldName := oldNames.get! i,
      oldType := oldTypes.get! i
      newType := newTypes.get! i
    };
    modifiers.push modifier
  ) #[] ;
  modifiers

/-- Once you've generalized a term "f" to its type, get all the necessary modifiers -/
def getNecesaryHypothesesForAutogeneralization  (thmType thmProof : Expr) (f : GeneralizedTerm) : MetaM (Array Modifier) := do
  let identifiersInProofType := getFreeIdentifiers thmType
  let identifiersInProofTerm := getFreeIdentifiers thmProof

  -- get all identifiers (that is, constants) in the proof term
  let identifierNames := identifiersInProofTerm--.removeAll identifiersInProofType
  let identifierTypes ← liftMetaM (identifierNames.mapM getTheoremStatement)

  -- only keep the ones that contain "f" (e.g. the multiplication symbol *) in their type
  let identifierNames ← identifierNames.filterM (fun i => do {let s ← getTheoremStatement i; containsExpr f.oldValue s})
  let identifierTypes ← identifierTypes.filterM (containsExpr f.oldValue)

  -- Now we need to replace every occurence of the specialized f (e.g. *) with the generalized f (e.g. a placeholder) in those identifiers.
  let generalizedIdentifierTypes ← identifierTypes.mapM (replaceCoarsely f.oldValue f.placeholder)

  -- return             old names     old types                  new types
  -- e.g.               mul_comm      ∀ n m : ℕ, n⬝m = m⬝n        ∀ n m : ℕ, f n m = f m n
  return makeModifiers identifierNames identifierTypes generalizedIdentifierTypes

/-- Find the proof of the new auto-generalized theorem -/
def autogeneralizeProof (thmProof : Expr) (modifiers : Array Modifier) (f : GeneralizedTerm) : MetaM Expr := do
  -- if the types has hypotheses in the order [h1, h2], then in the proof term they look like (fun h1 => ...(fun h2 => ...)), so h2 is done first.
  let modifiers := modifiers.reverse

  logInfo m!"The original proof: {thmProof}"

  -- add in the hypotheses, replacing old hypotheses names
  let genThmProof ← (modifiers.size).foldM
    (fun i acc => do
      let mod := modifiers.get! i
      logInfo m!"Proof so far: {acc}"
      logInfo m!"New hypothesis to add: {mod.newType}"
      let body ← replaceWithBVar (.const mod.oldName []) acc
      return .lam mod.newName mod.newType body .default

    ) thmProof ;
  logInfo m!"Proof with all added hypotheses {genThmProof}"

  -- add in f, replacing the old f
  --"withLocalDecl" temporarily adds "f.name : f.type" to context, storing the fvar in placeholder
  let genThmProof ← withLocalDecl f.name .default f.type (fun placeholder => do
    let body ← replaceCoarsely f.placeholder placeholder genThmProof
    mkLambdaFVars #[placeholder] body
  )

  return genThmProof

/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (fExpr : Expr): TacticM Unit := do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) := (← getHypothesisType thmName, ← getHypothesisProof thmName)

  -- Get details about the term we're going to generalize, to replace it with an arbitrary const of the same type
  let f : GeneralizedTerm := {oldValue := fExpr, name := `f, type := ← inferType fExpr, placeholder := ← mkFreshExprMVar (some (← inferType fExpr))}
  logInfo m!"The term to be generalized is {f.oldValue} with type {f.type}"

  -- Do the next bit of generalization -- figure out which hypotheses we need to add to make the generalization true
  let modifiers ← getNecesaryHypothesesForAutogeneralization thmType thmProof f
  logInfo m!"The first hypothesis needed was {modifiers[0]!.oldType}, which we'll now change to {modifiers[0]!.newType}"
  -- logInfo m!"The number of hypotheses needed to generalize this theorem is {modifiers.size}"

  -- Get the generalized theorem (with those additional hypotheses)
  let genThmProof ← autogeneralizeProof thmProof modifiers f; logInfo ("Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; logInfo ("Generalized Type: " ++ genThmType)

  createHypothesis genThmType genThmProof (thmName++`Gen)

  logInfo s!"Successfully generalized \n  {thmName} \nto \n  {thmName++`Gen} \nby abstracting \n  {← ppExpr fExpr}."

/- Autogeneralize term "t" in hypothesis "h"-/
elab "autogeneralize" h:ident f:term : tactic => do
  let f ← (Lean.Elab.Term.elabTerm f none)
  autogeneralize h.getId f



end Autogeneralize
