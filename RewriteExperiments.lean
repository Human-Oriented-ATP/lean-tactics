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


structure eqExprs where
  heq : Expr
  lhs : Expr
  rhs : Expr
  type : Expr


def range : Nat → List Nat
| 0 => []
| n + 1 => n :: range n


def matchEToLHS (mvarId : MVarId) (fVars : Array Expr) (e heq heqType : Expr) (symm : Bool := false) :
  MetaM (Expr × Expr × eqExprs × Array Expr × Array BinderInfo) := do
  let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
  let heq := mkAppN heq newMVars
  let cont (heq heqType : Expr) : MetaM (Expr × Expr × eqExprs × Array Expr × Array BinderInfo) := do
    match heqType.eq? with
    | none => throwTacticEx `rewrite mvarId m!"equality or iff proof expected{indentExpr heqType}"
    | some (type, lhs, rhs) =>
      let cont (heq lhs rhs : Expr) : MetaM (Expr × Expr × eqExprs × Array Expr × Array BinderInfo) := do

        if (← isDefEq lhs (e.instantiateRev fVars))
          then
          -- replace all these free variables with the original loose bound variables
            let heq := (← instantiateMVars heq).abstract fVars
            let lhs := (← instantiateMVars lhs).abstract fVars
            let rhs := (← instantiateMVars rhs).abstract fVars
            let type := (← instantiateMVars type).abstract fVars

            let n := fVars.size

            return ((range n).foldl (mkApp · <| .bvar ·) (.bvar n), rhs, {heq, lhs, rhs, type : eqExprs}, newMVars, binderInfos)
        else
          throwError "subexpression '{e.instantiateRev fVars}' does not match left hand side '{lhs}'"

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

def introduce_bvar (binderName : Name) (binderType : Expr) (rw : eqExprs) : MetaM eqExprs := do
  let heq' := .lam binderName binderType rw.heq .default
  let lhs := .lam binderName binderType rw.lhs .default
  let rhs := .lam binderName binderType rw.rhs .default
  let result_type := .lam binderName binderType rw.type .default
  let type := .forallE binderName binderType rw.type .default
  let heq := mkApp5 (.const `funext [← getLevel binderType, ← getLevel rw.type]) binderType result_type lhs rhs heq'
  return {heq, lhs, rhs, type}


def recurseToPosition (mvarId : MVarId) (e heq heqType : Expr) (position : List Nat) (symm : Bool) :
  MetaM (Expr × Expr × eqExprs × Array Expr × Array BinderInfo) :=
  
  let rec visit (e : Expr) (fVars : Array Expr) : List Nat → MetaM (Expr × Expr × eqExprs × Array Expr × Array BinderInfo)
    | [] => matchEToLHS mvarId fVars e heq heqType symm
    
    | x :: xs => do
      match x, e with
      | 0, .app f a          => let (e, eNew, rw) ← visit f fVars xs; return (.app e a, .app eNew a, rw)
      | 1, .app f a          => let (e, eNew, rw) ← visit a fVars xs; return (.app f e, .app f eNew, rw)

      | 0, .mdata d b        => let (e, eNew, rw) ← visit b fVars xs; return (.mdata d e, .mdata d eNew, rw)

      | 0, .proj n i b       => let (e, eNew, rw) ← visit b fVars xs; return (.proj n i e, .proj n i eNew, rw)

      | 0, .letE n t v b c   => let (e, eNew, rw) ← visit t fVars xs; return (.letE n e v b c, .letE n eNew v b c, rw)
      | 1, .letE n t v b c   => let (e, eNew, rw) ← visit v fVars xs; return (.letE n t e b c, .letE n t eNew b c, rw)
      | 2, .letE n t v b c   =>
        withLocalDeclD n (t.instantiateRev fVars) λ fVar ↦ do
        let (e, eNew, rw, z) ← visit b (fVars.push fVar) xs
        return (.letE n t v e c, .letE n t v eNew c, ← introduce_bvar n t rw, z)
                                                        
      | 0, .lam n t b bi     => let (e, eNew, rw) ← visit t fVars xs; return (.lam n e b bi, .lam n eNew b bi, rw)
      | 1, .lam n t b bi     =>
        withLocalDecl n bi (t.instantiateRev fVars) λ fVar ↦ do
        let (e, eNew, rw, z) ← visit b (fVars.push fVar) xs
        return (.lam n t e bi, .lam n t eNew bi, ← introduce_bvar n t rw, z)

      | 0, .forallE n t b bi => let (e, eNew, rw) ← visit t fVars xs; return (.forallE n e b bi, .forallE n eNew b bi, rw)
      | 1, .forallE n t b bi =>
        withLocalDecl n bi (t.instantiateRev fVars) λ fVar ↦ do
        let (e', eNew, rw, z) ← visit b (fVars.push fVar) xs
        return (.forallE n t e' bi, .forallE n t eNew bi, ← introduce_bvar n t rw, z)

      | _, _                => throwError "could not find branch {x} in subexpression '{e}'"
      
  visit e #[] position


def Lean.MVarId.myrewrite (mvarId : MVarId) (e heq : Expr) (position : List Nat) (symm : Bool) (config : Rewrite.Config) : MetaM RewriteResult := do
  mvarId.withContext do
    mvarId.checkNotAssigned `rewrite
    let heqType ← instantiateMVars (← inferType heq)

    let (eAbst, eNew, {heq, type, ..}, newMVars, binderInfos)
      ← withConfig (fun oldConfig => { config, oldConfig with }) <| recurseToPosition mvarId (← instantiateMVars e) heq heqType position symm

    let eEqE ← mkEq e e
    let eEqEAbst := mkApp eEqE.appFn! eAbst
    let motive := Lean.mkLambda `_a BinderInfo.default type eEqEAbst
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

  
def rewriteTarget' (position : List Nat) (stx : Syntax) (symm : Bool) (config : Rewrite.Config) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let heq ← elabTerm stx none true
    let r ← (← getMainGoal).myrewrite (← getMainTarget) heq position symm (config := config)
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


example (g : b = c) (h : ∀a, a = b) : ∀a, a = c := by
  rewriteAt [1,1] [← g] 
  exact h

example : ∀ n, n + 1 + 1 = n + 2 := by
  rewriteAt [1,0,1] [Nat.add_assoc]
  intro n
  rfl


def symm_iff : a = b ↔ b = a := ⟨Eq.symm, Eq.symm⟩ 
-- notice how this only works with the @ notation
example : ∀ n, (n = 1) = (1 = n) := by
  rewriteAt [1,0,1] [@symm_iff] -- @
  intro n
  rfl

example (h: ∀ n:ℕ, n = zero) : ∀ n:ℕ, n = zero := by
  rewriteAt [1,0,1] [h]
  intro _
  rfl
  


-- these work now :-)
example {p q : ℕ  → ℕ → Prop} (h₁ : a = b) (h₂ : ∀ q, q = p) : ∀ z : ℝ, (q b a → p a b) ∧ z = z := by
  rewriteAt [1,0,1,0,1] [h₁]
  rewriteAt [1,0,1,1,0,1] [h₁]
  rewriteAt [1,0,1,0,0,0] [h₂]
  rewriteAt [1,1] [fun a => iff_true_intro (@rfl _ a)] -- jovan: this is now possible
  exact λ _ ↦ ⟨id, trivial⟩

-- with ConvPanel mode
example {p q : ℕ  → ℕ → Prop} (h₁ : a = b) (h₂ : ∀ q, q = p) : ∀ z : ℝ, (q b a → p a b) ∧ z = z := by
  with_panel_widgets [SelectPanel]
    rewriteAt  [1, 0, 1, 1, 0, 1] [h₁]
    rewriteAt [1, 0, 1, 0, 1] [h₁]
    rewriteAt [1,0,1,0,0,0] [h₂]
    rewriteAt  [1, 0, 1] [iff_true_intro (id)]
    rewriteAt [1, 1] [fun a b => iff_true_intro (@rfl _ a)]
  exact λ _ ↦ ⟨trivial, trivial⟩
  exact ℕ 

