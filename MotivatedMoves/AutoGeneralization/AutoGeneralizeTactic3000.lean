import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic /- π -/
import Mathlib.Data.Real.Irrational

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize

/-- Getting theorems from context --/
def getTheoremStatement (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | throwError ("Could not find a theorem with name " ++ n) -- get the declaration with that name
  return thm.type -- return the theorem statement (the type is the proposition)

/-- Getting theorems from context --/
def isTheorem (n : Name) : MetaM Bool := do
  let some thm := (← getEnv).find? n | throwError ("Could not find a theorem with name " ++ n) -- get the declaration with that name
  return thm.hasValue -- returns true if it is a theorem or definition

/-- Getting theorems from context --/
def getTheoremProof (n : Name) : MetaM Expr := do
  let some thm := (← getEnv).find? n | throwError ("Could not find a theorem with name " ++ n) -- get the declaration with that name
  -- let pf ← thm.value?
  return thm.value! -- return the theorem statement (the term is the proof)

/- (For debugging) Print what type of expression something is -/
def printExprType (e : Expr) : MetaM Unit := do
  logInfo e.ctorName


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



#eval do {let e ← getTheoremStatement ``multPermute; logExpression e}

#eval getTheoremStatement ``multPermute
#eval do {let e ← getTheoremStatement ``multPermute; logPrettyExpression e}

#eval do {let e ← getTheoremStatement ``multPermute; logFormattedExpression e}
#eval do {let e ← getTheoremStatement ``multPermute; logExpressionType e}

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

/-- Gets all identifier names in an expression -/
def getFreeIdentifiers (e : Expr) : List Name := e.getUsedConstants.toList

-- TO DO: use traverseExpr to do this instead
/-- Creating replaces "original" with "replacement" in an expression -- as long as the subexpression found is definitionally equal to "original" -/
def replaceCoarsely (original : Expr) (replacement: Expr) : Expr → MetaM Expr :=
fun e => do
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

/- If a subexpression matches the given "condition", it is replaced with "replacement"-/
def replaceWhere (condition : Expr → Bool) (replacement: Expr) : Expr → MetaM Expr  :=
fun e => do
  if condition e
    then return replacement
  else
    match e with
    | Expr.forallE n d b bi  => return Expr.forallE n (← replaceWhere condition replacement d) (← replaceWhere condition replacement b) bi
    | Expr.lam n d b bi      => return Expr.lam n (← replaceWhere condition replacement d) (← replaceWhere condition replacement b) bi
    | Expr.app f a           => return Expr.app (← replaceWhere condition replacement f) (← replaceWhere condition replacement a)
    | Expr.letE n t v b x    => return Expr.letE n (← replaceWhere condition replacement t) (← replaceWhere condition replacement v) (← replaceWhere condition replacement b) x
    | misc                     => return misc -- no need to recurse

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
def replaceWithBVarWhere (condition : Expr → Bool) (e : Expr) (depth : Nat := 0) : MetaM Expr := do
  match e with
    | .lam n a b bi => return .lam n a (← replaceWithBVarWhere condition b (depth+1)) bi
    | .forallE n a b bi => return .forallE n a (← replaceWithBVarWhere condition b (depth+1)) bi
    | x =>  replaceWhere (condition) (.bvar depth) x


/-- Returns true if "e" contains "subexpr".  Differs from "occurs" because this uses the coarser "isDefEq" rather than "==" -/
def containsExpr(subexpr : Expr)  (e : Expr) : MetaM Bool := do
  let mctx ← getMCtx -- save metavar context before using isDefEq
  let e_subexprs := getSubexpressionsIn e
  let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return ← isDefEq e_subexpr subexpr)
  setMCtx mctx -- revert metavar context after using isDefEq, so this function doesn't have side-effects on the expr e
  return firstExprContainingSubexpr.isSome

/-- Returns the number of times "subexpr" occurs in "e". Uses the coarser "isDefEq" rather than "==" -/
def countOccurrencesOf (subexpr : Expr)  (e : Expr) : MetaM Nat := do
  -- save metavar context before using isDefEq
  let mctx ← getMCtx

  -- get everything that equals subexpr
  let e_subexprs := getSubexpressionsIn e
  let exprsEqToSubexpr ← (e_subexprs.filterM fun e_subexpr => return ← isDefEq e_subexpr subexpr)

  -- remove any expression strictly contained in another
  let filteredExprsEqToSubexpr ← exprsEqToSubexpr.filterM fun e1 =>
    not <$> exprsEqToSubexpr.anyM fun e2 => return e1 != e2 && e1.occurs e2 -- e1 is strictly contained in e2
  -- logInfo filteredExprsEqToSubexpr

  -- revert metavar context after using isDefEq, so this function doesn't have side-effects on the expr e
  setMCtx mctx
  -- return the length of that list of expressions
  return filteredExprsEqToSubexpr.length

#eval countOccurrencesOf (toExpr 2) (toExpr 2)
#eval countOccurrencesOf (toExpr 2) (toExpr 3)

#check Expr.occurs
-- /-- Returns true if "e" contains "subexpr". Uses '--'.  Same as 'occurs' -/
-- def containsExprStrict (subexpr : Expr)  (e : Expr) : MetaM Bool := do
--   let e_subexprs := getSubexpressionsIn e
--   let firstExprContainingSubexpr ← (e_subexprs.findM? fun e_subexpr => return e_subexpr == subexpr)
--   return firstExprContainingSubexpr.isSome

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
  -- newType : Expr                    -- the type that has the placeholder of "f"
deriving Inhabited

def makeModifiers (oldNames : List Name) (oldTypes: List Expr)  : Array Modifier :=
  let modifiers : Array Modifier := oldNames.length.fold (fun i (modifiers : Array Modifier) =>
    let modifier : Modifier := {
      oldName := oldNames.get! i,
      oldType := oldTypes.get! i
      -- newType := newTypes.get! i
    };
    modifiers.push modifier
  ) #[] ;
  modifiers


partial def kabstractConst (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  let e ← instantiateMVars e
  let pType ← inferType p
  -- let pHeadIdx := p.toHeadIndex
  -- let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) (offset : Nat) : StateRefT Nat MetaM Expr := do
    let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
      match e with
      | .app f a         => return e.updateApp! (← visit f offset) (← visit a offset)
      | .mdata _ b       => return e.updateMData! (← visit b offset)
      | .proj _ _ b      => return e.updateProj! (← visit b offset)
      | .letE _ t v b _  => return e.updateLet! (← visit t offset) (← visit v offset) (← visit b (offset+1))
      | .lam _ d b _     => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
      | .forallE _ d b _ => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
      | .const n _       => let constType ← getTheoremStatement n
                            if (← containsExpr p constType) then
                              let genConstType ← visit constType offset
                              let m ← mkFreshExprMVar genConstType
                              return m
                            else
                              return e
      | e                => return e
    if e.hasLooseBVars then
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
        let i ← get
        set (i+1)
        if occs.contains i then
          return ← mkFreshExprMVar pType -- replace every occurrence of pattern with mvar
        else
          -- Revert the metavariable context,
          -- so that other matches are still possible.
          setMCtx mctx
          visitChildren ()
      else
        visitChildren ()
  visit e 0 |>.run' 1

/- A slower, but more accurate version of kabstract.  It doesn't check if heads of expressions are equal before checking definitional equality. -/
def kabstractSlow (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  let e ← instantiateMVars e
  let pType ← inferType p
  if p.isFVar && occs == Occurrences.all then
    return e.abstract #[p] -- Easy case
  else
    -- let pHeadIdx := p.toHeadIndex
    -- let pNumArgs := p.headNumArgs
    let rec visit (e : Expr) (offset : Nat) : StateRefT Nat MetaM Expr := do
      let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
        match e with
        | .app f a         => return e.updateApp! (← visit f offset) (← visit a offset)
        | .mdata _ b       => return e.updateMData! (← visit b offset)
        | .proj _ _ b      => return e.updateProj! (← visit b offset)
        | .letE _ t v b _  => return e.updateLet! (← visit t offset) (← visit v offset) (← visit b (offset+1))
        | .lam _ d b _     => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
        | .forallE _ d b _ => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
        | e                => return e
      if e.hasLooseBVars then
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
          let i ← get
          set (i+1)
          if occs.contains i then
            return ← mkFreshExprMVar pType
          else
            -- Revert the metavariable context,
            -- so that other matches are still possible.
            setMCtx mctx
            visitChildren ()
        else
          visitChildren ()
    visit e 0 |>.run' 1

/- Replaces each instance of p in e with an mvar instead of a bvar-/
def kabstract' (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) (offset : Nat) : StateRefT Nat MetaM Expr := do
    let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
      match e with
      | .app f a         => return e.updateApp! (← visit f offset) (← visit a offset)
      | .mdata _ b       => return e.updateMData! (← visit b offset)
      | .proj _ _ b      => return e.updateProj! (← visit b offset)
      | .letE _ t v b _  => return e.updateLet! (← visit t offset) (← visit v offset) (← visit b (offset+1))
      | .lam _ d b _     => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
      | .forallE _ d b _ => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
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
          return ← mkFreshExprMVar (← inferType p)
        else
          -- Revert the metavariable context,
          -- so that other matches are still possible.
          setMCtx mctx
          visitChildren ()
      else
        visitChildren ()
  visit e 0 |>.run' 1

/-- Once you've generalized a term "f" to its type, get all the necessary modifiers -/
def getNecesaryHypothesesForAutogeneralization  (thmType thmProof : Expr) (f : GeneralizedTerm) : MetaM (Array Modifier) := do
  let identifiersInProofType := getFreeIdentifiers thmType
  let identifiersInProofTerm := getFreeIdentifiers thmProof

  -- get all identifiers (that is, constants) in the proof term
  let identifierNames := identifiersInProofTerm.removeAll identifiersInProofType
  let identifierTypes ← liftMetaM (identifierNames.mapM getTheoremStatement)

  -- only keep the ones that contain "f" (e.g. the multiplication symbol *) in their type
  logInfo m!"Old identifier names {identifierNames}"
  logInfo m!"Old identifier types {identifierTypes}"
  let identifierNames ← identifierNames.filterM (fun i => do {let s ← getTheoremStatement i; containsExpr f.oldValue s})
  let identifierTypes ← identifierTypes.filterM (containsExpr f.oldValue)
  logInfo m!"Filtered identifier names {identifierNames}"
  logInfo m!"Filtered identifier types {identifierTypes}"

  -- Now we need to replace every occurence of the specialized f (e.g. *) with the generalized f (e.g. a placeholder) in those identifiers.
  -- let generalizedIdentifierTypes ← identifierTypes.mapM (replaceCoarsely f.oldValue f.placeholder)

  -- return             old names     old types                  new types
  -- e.g.               mul_comm      ∀ n m : ℕ, n⬝m = m⬝n        ∀ n m : ℕ, f n m = f m n
  return makeModifiers identifierNames identifierTypes --generalizedIdentifierTypes

/-- Find the proof of the new auto-generalized theorem -/
def autogeneralizeProof (thmProof : Expr) (f : GeneralizedTerm) : MetaM Expr := do
  let abstractedProof ← kabstractConst thmProof f.oldValue -- replace instances of f's old value with metavariables

  return abstractedProof

  -- -- if the types has hypotheses in the order [h1, h2], then in the proof term they look like (fun h1 => ...(fun h2 => ...)), so h2 is done first.
  -- let modifiers := modifiers.reverse

  -- logInfo m!"The original proof: {thmProof}"

  -- -- add in the hypotheses, replacing old hypotheses names
  -- let genThmProof ← (modifiers.size).foldM
  --   (fun i acc => do
  --     let mod := modifiers.get! i
  --     logInfo m!"New hypothesis to add: {mod.oldType}"
  --     let body ← replaceWithBVarWhere (fun e => e.isConstOf mod.oldName) acc
  --     return .lam mod.newName mod.oldType body .default

  --   ) thmProof ;
  -- logInfo m!"Proof with all added hypotheses {genThmProof}"

  -- -- add in f, replacing the old f
  -- --"withLocalDecl" temporarily adds "f.name : f.type" to context, storing the fvar in placeholder
  -- let genThmProof ← withLocalDecl f.name .default f.type (fun placeholder => do
  --   logInfo m!"Before kabstract {genThmProof}"
  --   let body ← kabstractSlow genThmProof f.oldValue  -- turn f.oldValue into loose bvars
  --   logInfo m!"After kabstract {body}"
  --   let body := body.instantiate1 placeholder -- turn the loose bvars to the mvar placeholder
  --   mkLambdaFVars #[placeholder] body
  -- )
  -- logInfo m!"Proof with abstracted 'f' {genThmProof}"

  -- return genThmProof



/-- Generate a term "f" in a theorem to its type, adding in necessary identifiers along the way -/
def autogeneralize (thmName : Name) (fExpr : Expr): TacticM Unit := do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) := (← getHypothesisType thmName, ← getHypothesisProof thmName)

  -- Get details about the term we're going to generalize, to replace it with an arbitrary const of the same type
  let f : GeneralizedTerm := {oldValue := fExpr, name := `f, type := ← inferType fExpr, placeholder := ← mkFreshExprMVar (some (← inferType fExpr))}
  logInfo m!"The term to be generalized is {f.oldValue} with type {f.type}"

  -- Do the next bit of generalization -- figure out which hypotheses we need to add to make the generalization true
  -- let modifiers ← getNecesaryHypothesesForAutogeneralization thmType thmProof f
  -- logInfo m!"The number of hypotheses needed to generalize this theorem is {modifiers.size}"

  -- -- Get the generalized theorem (with those additional hypotheses)
  let genThmProof ← autogeneralizeProof thmProof f; logInfo ("Generalized Proof: " ++ genThmProof)
  let genThmType ← inferType genThmProof; logInfo ("Generalized Type: " ++ genThmType)

  -- get the generalized type from user
  let userThmType ← kabstract thmType f.oldValue (occs:= .pos [1])
  let userThmType := userThmType.instantiate1 (← mkFreshExprMVar f.type)
  -- compare
  let unif ← isDefEq genThmType userThmType
  logInfo m!"Do they unify? {unif}"
  logInfo m!"Instantiated genThmType: {← instantiateMVars genThmType}"
  logInfo m!"Instantiated userThmType: {← instantiateMVars userThmType}"
  logInfo m!"Instantiated proof after type was inferred: {← instantiateMVars genThmProof}"
  -- createHypothesis genThmType genThmProof (thmName++`Gen)

  -- logInfo s!"Successfully generalized \n  {thmName} \nto \n  {thmName++`Gen} \nby abstracting \n  {← ppExpr fExpr}."

/- Autogeneralize term "t" in hypothesis "h"-/
elab "autogeneralize" h:ident f:term : tactic => do
  let f ← (Lean.Elab.Term.elabTerm f none)
  autogeneralize h.getId f


elab "kabstract_test" : term => do
  let stx ← `(2+2+3)
  let e ← Term.elabTerm stx none
  let abstractedBody ← kabstract e (toExpr 2) (occs := .pos [1])
  return .lam `x (.const `Nat []) abstractedBody .default

#check kabstract_test

-- Turns each instance of `pattern` in `e` into a different metavariable.`
def abstractToDifferentMVars (e : Expr) (pattern : Expr) :  MetaM Expr := sorry -- this is our personalized kabstract

-- Given a Proof Type with one constant turned into a metavariable
-- Return the Proof Term with all the "tied-together" constants turned into the same metavariable
def getAbstractedProofTerm (abstractedProofType : Expr) : MetaM Expr := sorry

-- elab "putHolesInProof"

def turnAllOccurencesIntoDifferentMetavariables (pattern : Expr) (e : Expr) : TacticM Expr :=
  kabstract' e pattern

/- For any mvars in e2 that unify with mvars in e1, replace them to be the ones in e1 -/
-- def linkMVars (e1 : Expr) (e2 : Expr) : MetaM Expr := do
--   return e1

elab "replacePatternWithHoles" h:ident pattern:term : tactic => withMainContext do
  let hType ← getHypothesisType h.getId
  let hTerm ← getHypothesisProof h.getId

  let pattern ← Term.elabTermAndSynthesize pattern none

  let holeyHType ← turnAllOccurencesIntoDifferentMetavariables  pattern hType
  let holeyHTerm ← turnAllOccurencesIntoDifferentMetavariables  pattern hTerm

  logInfo m!"After abstraction type {holeyHType}"
  logInfo m!"After abstraction term {holeyHTerm}"
  logInfo m!"After abstraction inferredType of term {← inferType holeyHTerm}"

  -- logInfo m!"After abstraction.  {holeyHType} := {holeyHTerm}"

end Autogeneralize
