import Lean.Data.Occurrences
import Lean.HeadIndex
import Lean.Meta.Basic
import Lean.SubExpr
import Lean.Meta.Tactic.Rewrite
import Lean.Elab.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config

open Lean Meta Elab Tactic Parser.Tactic

-- write a version of `kabstract` where we take in `SubExpr.Pos` and replace that position with a `bvar`
/--Abstract occurrences of `p` in `e`. We detect subterms equivalent to `p` using key-matching.
That is, only perform `isDefEq` tests when the head symbol of substerm is equivalent to head symbol of `p`.
By default, all occurrences are abstracted, but this behavior can be controlled using the `occs` parameter.
-/
def kabstract' (e : Expr) (p : Expr) (position : List Nat) : MetaM Expr := do
  let e ← instantiateMVars e
  --if p.isFVar then
  --  return e.abstract #[p] -- Easy case
  let rec visit (pos: List Nat) (e : Expr) (offset : Nat) : MetaM Expr := do
    let visitChild (pos' : List Nat) : Nat → MetaM Expr := fun n => do
      match n, e with
      | 0, .app f a         => return .app (← visit pos' f offset) a
      | 1, .app f a         => return .app f (← visit pos' a offset)
      | 0, .mdata d b       => return .mdata d (← visit pos' b offset)
      | 0, .proj s i b      => return .proj s i (← visit pos' b offset)
      | 0, .letE a t v b c  => return .letE a (← visit pos' t offset) v b c
      | 1, .letE a t v b c  => return .letE a t (← visit pos' v offset) b c
      | 2, .letE a t v b c  => return .letE a t v (← visit pos' b (offset+1)) c
      | 0, .lam a d b c     => return .lam a (← visit pos' d offset) b c
      | 1, .lam a d b c     => return .lam a d (← visit pos' b (offset+1)) c
      | 0, .forallE a d b c => return .forallE a (← visit pos' d offset) b c
      | 1, .forallE a d b c => return .forallE a d (← visit pos' b (offset+1)) c
      | _, _                => throwError "empty string"

    match pos with 
    | [] => if (← isDefEq e p) 
            then return .bvar offset
            else throwError "empty string"
    | x :: xs => visitChild xs x 
  visit position e 0

/--
Rewrite goal `mvarId`
-/

def _root_.Lean.MVarId.rewrite' (mvarId : MVarId) (e : Expr) (heq : Expr) (position : List Nat)
    (symm : Bool := false) (config := { : Rewrite.Config }) : MetaM RewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `rewrite
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let cont (heq heqType : Expr) : MetaM RewriteResult := do
      match (← matchEq? heqType) with
      | none => throwTacticEx `rewrite mvarId m!"equality or iff proof expected{indentExpr heqType}"
      | some (α, lhs, rhs) =>
        let cont (heq heqType lhs rhs : Expr) : MetaM RewriteResult := do
          if lhs.getAppFn.isMVar then
            throwTacticEx `rewrite mvarId m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
          let e ← instantiateMVars e
          let eAbst ← withConfig (fun oldConfig => { config, oldConfig with }) <| kabstract' e lhs position
          unless eAbst.hasLooseBVars do
            throwTacticEx `rewrite mvarId m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
          -- construct rewrite proof
          let eNew := eAbst.instantiate1 rhs
          let eNew ← instantiateMVars eNew
          let eEqE ← mkEq e e
          let eEqEAbst := mkApp eEqE.appFn! eAbst
          let motive := Lean.mkLambda `_a BinderInfo.default α eEqEAbst
          unless (← isTypeCorrect motive) do
            throwTacticEx `rewrite mvarId "motive is not type correct"
          let eqRefl ← mkEqRefl e
          let eqPrf ← mkEqNDRec motive eqRefl heq
          postprocessAppMVars `rewrite mvarId newMVars binderInfos
          let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
          let otherMVarIds ← getMVarsNoDelayed eqPrf
          let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
          let newMVarIds := newMVarIds ++ otherMVarIds
          pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
        match symm with
        | false => cont heq heqType lhs rhs
        | true  => do
          let heq ← mkEqSymm heq
          let heqType ← mkEq rhs lhs
          cont heq heqType rhs lhs
    match heqType.iff? with
    | some (lhs, rhs) =>
      let heqType ← mkEq lhs rhs
      let heq := mkApp3 (mkConst `propext) lhs rhs heq
      cont heq heqType
    | none =>
      cont heq heqType
  
def rewriteTarget' (position : List Nat) (stx : Syntax) (symm : Bool) (config : Rewrite.Config) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).rewrite' (← getMainTarget) e position symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

-- declare_config_elab elabRewriteConfig Rewrite.Config

syntax (name := rewriteSeq') "rewrite" "[" num,* "]" (config)? rwRuleSeq (location)? : tactic

@[tactic rewriteSeq'] def evalRewriteSeq : Tactic := fun stx => do
  let cfg ← Tactic.elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      -- change the next line to `rewriteTarget'` and extract the `List Nat` from `num, *`
      (rewriteTarget term symm cfg)
      (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")