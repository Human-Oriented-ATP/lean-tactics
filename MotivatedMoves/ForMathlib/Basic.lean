import Lean
import ProofWidgets

open Lean Meta Server ProofWidgets Elab Tactic Parser Tactic

section 

-- from Lean/Elab/Tactic/Conv/Pattern
def expandPattern (p : Term) : TermElabM AbstractMVarsResult :=
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
       Term.withoutModifyingElabMetaStateWithInfo <| withRef p <|
       Term.withoutErrToSorry do
         abstractMVars (← Term.elabTerm p none)

open Parser Tactic Conv in
def expandOccs : Option (TSyntax ``occs) → Occurrences
  | none => .all
  | some occs =>
    match occs with
      | `(occs| (occs := *)) => .all
      | `(occs| (occs := $ids*)) => .pos <| ids.map (TSyntax.getNat) |>.toList        
      | _ => .neg [] -- garbage

def Lean.Elab.Tactic.liftMetaTactic1' (tactic : MVarId → MetaM MVarId) : TacticM Unit :=
  liftMetaTactic <| fun mvarId ↦ do return [← tactic mvarId]

end

section

def SubExpr.patternAt (p : SubExpr.Pos) (root : Expr) : MetaM Expr := do  
  let e ← Core.viewSubexpr p root
  let binders ← Core.viewBinders p root
  let mvars ← binders.mapM fun (name, type) ↦ 
    mkFreshExprMVar type (userName := name)
  return e.instantiateRev mvars

def SubExpr.display (p : SubExpr.Pos) (root : Expr) : MetaM String := do
  let fmt ← PrettyPrinter.ppExpr <| ← SubExpr.patternAt p root
  return fmt.pretty

open PrettyPrinter Delaborator SubExpr in
@[delab mvar]
def delabMVarWithType : Delab := do
  let Expr.mvar n ← getExpr | unreachable!
  let type ← delab <| ← inferType <| ← getExpr
  let mvarDecl ← n.getDecl
  let n :=
    match mvarDecl.userName with
    | Name.anonymous => n.name.replacePrefix `_uniq `m
    | n => n.getRoot -- TODO: This may not be hygienic
  `((?$(mkIdent n) : $type))

-- based on `kabstract`
-- optionally specializes the pattern before finding its occurrence
def findMatchingOccurrence (position : SubExpr.Pos) (root : Expr) (pattern : Expr) : MetaM Nat := do
  let root ← instantiateMVars root
  unless ← isDefEq pattern (← SubExpr.patternAt position root) do
    throwError s!"The specified pattern does not match the pattern at position {position}."
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
      | e                => failure
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
  return occ

def findOccurrence (position : SubExpr.Pos) (root : Expr) : MetaM Nat := do
  let pattern ← SubExpr.patternAt position root
  findMatchingOccurrence position root pattern 

end

section

def Lean.FVarId.getUserNames (fvarId : FVarId) (goal : Widget.InteractiveGoal) : Array String :=
  let hyps := goal.hyps.filter (·.fvarIds.contains fvarId)
  hyps.concatMap (·.names)

def Lean.SubExpr.GoalsLocation.toSubExpr : SubExpr.GoalsLocation → MetaM SubExpr 
  | ⟨mvarId, .hyp fvarId⟩ => mvarId.withContext do
      return ⟨← fvarId.getType, .fromString! "/"⟩
  | ⟨mvarId, .hypType fvarId pos⟩ => mvarId.withContext do 
      return ⟨← fvarId.getType, pos⟩
  | ⟨mvarId, .hypValue fvarId pos⟩ => mvarId.withContext do
      let .some val ← fvarId.getValue? | unreachable!
      return ⟨val, pos⟩
  | ⟨mvarId, .target pos⟩ => do return ⟨← mvarId.getType, pos⟩

def Lean.SubExpr.GoalLocation.render (goal : Widget.InteractiveGoal) : SubExpr.GoalLocation → String
  | .hyp fvarId => renderLocation (fvarId.getUserNames goal) false
  | .hypType fvarId _ => renderLocation (fvarId.getUserNames goal) false
  | .hypValue fvarId _ => "" -- TODO: Handle this case
  | .target _ => ""
where 
  renderLocation (hyps : Array String) (type : Bool) : String :=
    "at " ++ " ".intercalate hyps.toList ++ (if type then " ⊢" else "")

end

structure InteractiveTacticProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
deriving RpcEncodable