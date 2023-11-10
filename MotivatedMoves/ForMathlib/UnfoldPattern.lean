import Lean
import Std.Lean.Position
import MotivatedMoves.ForMathlib.Basic

open Lean Core Meta MonadExceptOf Elab Tactic

section
-- Jovan's `tree_rewrite_def`

partial def reduceProjection (e : Expr) : ExceptT MessageData MetaM Expr :=
  e.withAppRev fun f revArgs => match f with
    | .proj _ i b => do
      let some value ← project? b i | throw m! "could not project expression {b}"
      reduceProjection (value.betaRev revArgs)
    | _ => return e

def replaceByDefAux (e : Expr) : ExceptT MessageData MetaM Expr := do
  if let .letE _ _ v b _ := e then return b.instantiate1 v
  e.withAppRev fun f revArgs => match f with
    | .const name us => do
      let info ← getConstInfoDefn name
      let result := info.value.instantiateLevelParams info.levelParams us
      if ← isDefEq result f then
        reduceProjection (result.betaRev revArgs)
      else
        throw m! "could not replace {f} by its definition"
    | _ => do
      let result ← reduceProjection (f.betaRev revArgs)
      if result == e then throw m! "could not find a definition for {e}"
      else return result

--

def replaceByDef (e : Expr) (pattern : AbstractMVarsResult) (occs : Occurrences) : MetaM Expr := do 
  let (_, _, p) ← openAbstractMVarsResult pattern
  let eAbst ← kabstract e p occs
  unless eAbst.hasLooseBVars do
    throwError m!"Failed to find instance of pattern {indentExpr p} in {indentExpr e}."
  match ← replaceByDefAux p with
  | .ok q =>
    let e' := eAbst.instantiate1 q
    instantiateMVars e'
  | .error err => throwError err

end

open Parser Tactic Conv

-- from Lean/Elab/Tactic/Conv/Pattern
def expandPattern (p : Term) : TermElabM AbstractMVarsResult :=
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
       Term.withoutModifyingElabMetaStateWithInfo <| withRef p <|
       Term.withoutErrToSorry do
         abstractMVars (← Term.elabTerm p none)

def expandOccs : Option (TSyntax ``occs) → Occurrences
  | none => .all
  | some occs =>
    match occs with
      | `(occs| (occs := *)) => .all
      | `(occs| (occs := $ids*)) => .pos <| ids.map (TSyntax.getNat) |>.toList        
      | _ => .neg [] -- garbage

def Lean.Elab.Tactic.liftMetaTactic1' (tactic : MVarId → MetaM MVarId) : TacticM Unit :=
  liftMetaTactic <| fun mvarId ↦ do return [← tactic mvarId]

elab "unfold'" occs:(occs)? p:term loc:(location)? : tactic => do
  let pattern ← expandPattern p
  let location := (expandLocation <$> loc).getD (.targets #[] true)
  let occurrences := expandOccs occs
  let goal ← getMainGoal
  goal.withContext do 
    withLocation location
      (atLocal := fun fvarId ↦ do
        let hypType ← fvarId.getType
        let newGoal ← goal.replaceLocalDeclDefEq fvarId <| ← 
          replaceByDef hypType pattern occurrences
        replaceMainGoal [newGoal])
      (atTarget := do
        let newGoal ← goal.replaceTargetDefEq <| ←
          replaceByDef (← goal.getType) pattern occurrences  
        replaceMainGoal [newGoal])
      (failed := (throwTacticEx `unfold · m!"Failed to unfold pattern {p}."))

def f := Nat.add

def g (n : Nat) := n + 2

def SubExpr.display (p : SubExpr.Pos) (root : Expr) : MetaM String := do
  let e ← Core.viewSubexpr p root
  let binders ← Core.viewBinders p root
  let mvars ← binders.mapM fun (name, type) ↦ 
    mkFreshExprMVar type (userName := name)
  let e' := e.instantiateRev mvars
  let fmt ← PrettyPrinter.ppExpr e'
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

#eval show TermElabM _ from do
  let s ← `(term| ∀ n m : Nat, n + m = m + n)
  let e ← Term.elabTerm s none
  SubExpr.display (.fromString! "/1/1") e

example (h : f 0 0 = g (1 + 1)) : f 0 1 = f 1 1 := by
  unfold' (occs := 1 2) f ?n ?n
  unfold' (occs := 1) f at h
  -- unfold' (occs := 1) (_ : Nat → Nat) (1 + 1) at h
  sorry
