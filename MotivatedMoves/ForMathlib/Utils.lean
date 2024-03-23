import Lean
import ProofWidgets

open Lean Meta Server ProofWidgets Elab Tactic Parser Tactic

/-!

# Utilities

Basic programming and meta-programming utilities for point-and-click tactics.

These include:
- Functions for expanding certain pieces of syntax into their corresponding expressions
- Code for viewing, rendering and finding the occurrences of patterns in expressions
- Code for converting `SubExpr.GoalsLocation` into expressions and strings.

-/

section

/-- Expand a term representing a pattern as an expression with meta-variables.
    This follows code from `Lean/Elab/Tactic/Conv/Pattern.lean`. -/
def expandPattern (p : Term) : TermElabM AbstractMVarsResult :=
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
    Term.withoutModifyingElabMetaStateWithInfo <| withRef p <|
    Term.withoutErrToSorry do
      abstractMVars (← Term.elabTerm p none)

open Parser Tactic Conv in
/-- Expand syntax of type `occs` into `Occurrences`. -/
def expandOccs : Option (TSyntax ``occs) → Occurrences
  | none => .all
  | some occs =>
    match occs with
      | `(occs| (occs := *)) => .all
      | `(occs| (occs := $ids*)) => .pos <| ids.map TSyntax.getNat |>.toList
      | _ => panic! s!"Invalid syntax {occs} for occurrences."

end

section

/-- The pattern at a given position in an expression.
    Variables under binders are turned into meta-variables in the pattern. -/
def SubExpr.patternAt (p : SubExpr.Pos) (root : Expr) : MetaM Expr := do
  let e ← Core.viewSubexpr p root
  let binders ← Core.viewBinders p root
  let mvars ← binders.mapM fun (name, type) ↦
    mkFreshExprMVar type (userName := name)
  return e.instantiateRev mvars

/-- Display the pattern at a given position in an expression as a string. -/
def SubExpr.display (p : SubExpr.Pos) (root : Expr) : MetaM String := do
  let fmt ← PrettyPrinter.ppExpr <| ← SubExpr.patternAt p root
  return fmt.pretty

open PrettyPrinter Delaborator SubExpr in
/-- A custom delaborator for meta-variables to preserve type information while displaying. -/
@[delab mvar] def delabMVarWithType : Delab := do
  let Expr.mvar n ← getExpr | unreachable!
  let type ← delab <| ← inferType <| ← getExpr
  let mvarDecl ← n.getDecl
  let n :=
    match mvarDecl.userName with
    | Name.anonymous => n.name.replacePrefix `_uniq `m
    | n => n.getRoot -- the root of the name; this operation may not be hygienic
  `((?$(mkIdent n) : $type))

/-- Finds the occurrence number of the pattern in the expression
    that matches the sub-expression at the specified position.
    This follows the structure of `kabstract` from Lean core. -/
def findMatchingOccurrence (position : SubExpr.Pos) (root : Expr) (pattern : Expr) : MetaM (Option Occurrences) := do
  let root ← instantiateMVars root
  unless ← isDefEq pattern (← SubExpr.patternAt position root) do
    return none
  let pattern ← instantiateMVars pattern
  let pHeadIdx := pattern.toHeadIndex
  let pNumArgs := pattern.headNumArgs
  let rec visit (e : Expr) (p : SubExpr.Pos) (offset : Nat) : StateRefT Nat (OptionT MetaM) Unit := do
    let visitChildren : Unit → StateRefT Nat (OptionT MetaM) Unit := fun _ => do
      match e with
      | .app f a         => do
        visit f p.pushAppFn offset <|>
        visit a p.pushAppArg offset
      | .mdata _ b       => visit b p offset
      | .proj _ _ b      => visit b p.pushProj offset
      | .letE _ t v b _  => do
        visit t p.pushLetVarType offset <|>
        visit v p.pushLetValue offset <|>
        visit b p.pushLetBody (offset+1)
      | .lam _ d b _     => do
        visit d p.pushBindingDomain offset <|>
        visit b p.pushBindingBody (offset+1)
      | .forallE _ d b _ => do
        visit d p.pushBindingDomain offset <|>
        visit b p.pushBindingBody (offset+1)
      | _                => failure
    if e.hasLooseBVars then
      visitChildren ()
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren ()
    else if (← isDefEq e pattern) then
      let i ← get
      set (i+1)
      if p = position then
        return ()
      else
        visitChildren ()
    else
      visitChildren ()
  let .some (_, occ) ← visit root .root 0 |>.run 0 |
    throwError s!"Could not find pattern at specified position {position}."
  return Occurrences.pos [occ]

/-- Finds the occurrence number of the pattern at
    the specified position in the whole expression. -/
def findOccurrence (position : SubExpr.Pos) (root : Expr) : MetaM (Option Occurrences) := do
  let pattern ← SubExpr.patternAt position root
  findMatchingOccurrence position root pattern

end

section

/-- The usernames in the same hypothesis bundle as `fvarId` (see `InteractiveHypothesisBundle`). -/
def Lean.FVarId.getUserNames (fvarId : FVarId) (goal : Widget.InteractiveGoal) : Array String :=
  let hyps := goal.hyps.filter (·.fvarIds.contains fvarId)
  hyps.concatMap (·.names)

/-- The `Expr` at a `SubExpr.GoalsLocation`. -/
def Lean.SubExpr.GoalsLocation.expr : SubExpr.GoalsLocation → MetaM Expr
  | ⟨mvarId, .hyp fvarId⟩        => mvarId.withContext fvarId.getType
  | ⟨mvarId, .hypType fvarId _⟩  => mvarId.withContext fvarId.getType
  | ⟨mvarId, .hypValue fvarId _⟩ => mvarId.withContext do return (← fvarId.getDecl).value
  | ⟨mvarId, .target _⟩          => mvarId.getType

/-- A `SubExpr.GoalsLocation` as a `SubExpr`. -/
def Lean.SubExpr.GoalsLocation.pos : SubExpr.GoalsLocation → SubExpr.Pos
  | ⟨_, .hyp _⟩          => .root
  | ⟨_, .hypType _ pos⟩  => pos
  | ⟨_, .hypValue _ pos⟩ => pos
  | ⟨_, .target pos⟩     => pos

/-- Rendering a `SubExpr.GoalLocation` as a `String`. -/
def Lean.SubExpr.GoalLocation.render
    (goal : Widget.InteractiveGoal) : SubExpr.GoalLocation → String
  | .hyp fvarId => renderLocation (fvarId.getUserNames goal) false
  | .hypType fvarId _ => renderLocation (fvarId.getUserNames goal) false
  | .hypValue _fvarId _ => panic! "Unable to operate on `let`-value" -- TODO: handle this case
  | .target _ => ""
where
  renderLocation (hyps : Array String) (type : Bool) : String :=
    " at " ++ " ".intercalate hyps.toList ++ (if type then " ⊢" else "")

end

/-- `Props` for interactive tactics.
    Keeps track of the range in the text document of the piece of syntax to replace. -/
structure InteractiveTacticProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
deriving RpcEncodable
