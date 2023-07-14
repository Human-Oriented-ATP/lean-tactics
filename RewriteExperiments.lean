import Lean.Data.Occurrences
import Lean.HeadIndex
import Lean.Meta.Basic
import Lean.SubExpr
import Lean.Meta.Tactic.Rewrite
import Lean.Elab.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
import ConvPanelUpdated
import Std.Data.List.Basic

open Lean Meta Elab Tactic Parser.Tactic

-- we take in `List Nat` and replace that position with a `bvar`

def kabstract' (e : Expr) (p : Expr) (position : List Nat) : MetaM Expr := do
  let e ← instantiateMVars e
-- if e.hasLooseBVars then
--        visitChildren ()
  let rec visit (e : Expr) (offset : Nat) : List Nat → MetaM Expr
    | [] => do
      if !e.hasLooseBVars
        then 
          if (← isDefEq e p) 
          then return .bvar offset
          else throwError "subexpression '{e}' does not match left hand side '{p}'"
      else 
        throwError "subexpression '{e}' has loose bounded variables" -- not sure what error to throw here
    | x :: xs => do
      match x, e with
      | 0, .app f a         => return .app (← visit f offset xs) a
      | 1, .app f a         => return .app f (← visit a offset xs)
      | 0, .mdata d b       => return .mdata d (← visit b offset xs)
      | 0, .proj s i b      => return .proj s i (← visit b offset xs)
      | 0, .letE a t v b c  => return .letE a (← visit t offset xs) v b c
      | 1, .letE a t v b c  => return .letE a t (← visit v offset xs) b c
      | 2, .letE a t v b c  => return .letE a t v (← visit b (offset+1) xs) c
      | 0, .lam a d b c     => return .lam a (← visit d offset xs) b c
      | 1, .lam a d b c     => return .lam a d (← visit b (offset+1) xs) c
      | 0, .forallE a d b c => return .forallE a (← visit d offset xs) b c
      | 1, .forallE a d b c => return .forallE a d (← visit b (offset+1) xs) c
      | _, _                => throwError "could not find branch {x} in subexpression '{e}'"
      
  visit e 0 position

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
        let cont (heq lhs rhs : Expr) : MetaM RewriteResult := do
          -- if lhs.getAppFn.isMVar then
          --   throwTacticEx `rewrite mvarId m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
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
        | false => cont heq lhs rhs
        | true  => do
          let heq ← mkEqSymm heq
          cont heq rhs lhs
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

def get_positions : List Syntax → List Nat
| [] => []
| x :: xs =>
  let rec go : List Syntax → List Nat
    | [] => []
    | _ :: y :: ys => TSyntax.getNat ⟨y⟩ :: go ys
    | _ => panic! "even length nonempy list"
  TSyntax.getNat ⟨x⟩ :: go xs


syntax (name := rewriteSeq') "rewriteAt" "[" num,* "]" (config)? rwRuleSeq (location)? : tactic

@[tactic rewriteSeq'] def evalRewriteSeq : Tactic := fun stx => do
  let list := (stx[2].getArgs.toList)
  unless List.length list % 2 == 1 do
    throwTacticEx `rewriteAt (← getMainGoal)  m!"even length list"
  let position := get_positions (stx[2].getArgs.toList)
  let cfg ← Tactic.elabRewriteConfig stx[4]
  let loc   := expandOptLocation stx[6]
  withRWRulesSeq stx[0] stx[5] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      -- change the next line to `rewriteTarget'` and extract the `List Nat` from `num, *`
      (rewriteTarget' position term symm cfg)
      (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")

--observe the strange behaviour when rewriting loose bound variables, by rewriteAt 1,1 [iff_true_intro]
example {p q : ℕ  → ℕ → Prop} (h₁ : a = b) (h₂ : ∀ q, q = p) : ∀ z : ℝ, (q b a → p a b) ∧ z = z := by
  rewriteAt [1,0,1,1,0,1] [h₁]
  rewriteAt [1,0,1,0,1] [h₁]
  rewriteAt [1,0,1,0,0,0] [h₂]
  -- rewriteAt [1,1] [iff_true_intro] -- mantas: no longer allowed and errors
  exact λ _ ↦ ⟨id, rfl⟩

-- with ConvPanel mode
example {p q : ℕ  → ℕ → Prop} (h₁ : a = b) (h₂ : ∀ q, q = p) : ∀ z : ℝ, (q b a → p a b) ∧ z = z := by
  with_panel_widgets [SelectPanel]
    rewriteAt  [1, 0, 1, 1, 0, 1] [h₁]
    rewriteAt [1, 0, 1, 0, 1] [h₁]
    sorry

