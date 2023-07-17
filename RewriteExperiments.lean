import Lean.Data.Occurrences
import Lean.HeadIndex
import Lean.Meta.Basic
import Lean.SubExpr
import Lean.Meta.Tactic.Rewrite
import Lean.Elab.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
import ProofWidgets.Component.SelectInsertPanel
import Lean.Meta.ExprLens

open Lean Meta Elab Tactic Parser.Tactic


structure eqExprs where
  heq : Expr
  type : Expr


def range : Nat → List Nat
| 0 => []
| n + 1 => n :: range n


def matchEToLHS (mvarId : MVarId) (fVars : Array Expr) (e : Expr) (stx : Syntax) (symm : Bool := false) :
  TacticM (Expr × Expr × Expr × Expr × Array Expr × Array BinderInfo) := do
  let heq ← elabTerm stx none true
  let heqType ← instantiateMVars (← inferType heq)
  let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
  let heq := mkAppN heq newMVars
  let cont (heq heqType : Expr) : MetaM (Expr × Expr × Expr × Expr × Array Expr × Array BinderInfo) := do
    match heqType.eq? with
    | none => throwTacticEx `rewrite mvarId m!"equality or iff proof expected{indentExpr heqType}"
    | some (type, lhs, rhs) =>
      let cont (heq lhs rhs : Expr) : MetaM (Expr × Expr × Expr × Expr × Array Expr × Array BinderInfo) := do

        if (← isDefEq lhs (e.instantiateRev fVars))
          then
            let mut heq ← instantiateMVars heq
            for fVar in fVars do
              heq ← mkAppM `funext #[← mkLambdaFVars #[fVar] heq]

            let rhs := (← instantiateMVars rhs).abstract fVars
            let type ← mkForallFVars fVars.reverse (← instantiateMVars type)

            let n := fVars.size

            return ((List.range n).foldl (mkApp · <| .bvar ·) (.bvar n), rhs, heq, type, newMVars, binderInfos)
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

def recurseToPosition (mvarId : MVarId) (e : Expr) (stx : Syntax) (position : List Nat) (symm : Bool) :
  TacticM (Expr × Expr × Expr × Expr × Array Expr × Array BinderInfo) :=
  
  let rec visit (e : Expr) (fVars : Array Expr) : List Nat → TacticM (Expr × Expr × Expr × Expr × Array Expr × Array BinderInfo)
    | [] => matchEToLHS mvarId fVars e stx symm
    
    | x :: xs => do
      match x, e with
      | 0, .app f a          => let (e, eNew, z) ← visit f fVars xs; return (.app e a, .app eNew a, z)
      | 1, .app f a          => let (e, eNew, z) ← visit a fVars xs; return (.app f e, .app f eNew, z)

      | 0, .mdata d b        => let (e, eNew, z) ← visit b fVars xs; return (.mdata d e, .mdata d eNew, z)

      | 0, .proj n i b       => let (e, eNew, z) ← visit b fVars xs; return (.proj n i e, .proj n i eNew, z)

      | 0, .letE n t v b c   => let (e, eNew, z) ← visit t fVars xs; return (.letE n e v b c, .letE n eNew v b c, z)
      | 1, .letE n t v b c   => let (e, eNew, z) ← visit v fVars xs; return (.letE n t e b c, .letE n t eNew b c, z)
      | 2, .letE n t v b c   =>
        withLocalDeclD n (t.instantiateRev fVars) λ fVar ↦ do
        let (e, eNew, z) ← visit b (fVars.push fVar) xs
        return (.letE n t v e c, .letE n t v eNew c, z)
                                                        
      | 0, .lam n t b bi     => let (e, eNew, z) ← visit t fVars xs; return (.lam n e b bi, .lam n eNew b bi, z)
      | 1, .lam n t b bi     =>
        withLocalDecl n bi (t.instantiateRev fVars) λ fVar ↦ do
        let (e, eNew, z) ← visit b (fVars.push fVar) xs
        return (.lam n t e bi, .lam n t eNew bi, z)

      | 0, .forallE n t b bi => let (e, eNew, z) ← visit t fVars xs; return (.forallE n e b bi, .forallE n eNew b bi, z)
      | 1, .forallE n t b bi =>
        withLocalDecl n bi (t.instantiateRev fVars) λ fVar ↦ do
        let (e', eNew, z) ← visit b (fVars.push fVar) xs
        return (.forallE n t e' bi, .forallE n t eNew bi, z)

      | _, _                => throwError "could not find branch {x} in subexpression '{e}'"
      
  visit e #[] position


def Lean.MVarId.rewrite' (mvarId : MVarId) (e : Expr) (stx : Syntax) (position : List Nat) (symm : Bool) (config : Rewrite.Config) : TacticM RewriteResult := do
  mvarId.withContext do
    mvarId.checkNotAssigned `rewrite

    let (eAbst, eNew, heq, type, newMVars, binderInfos)
      ← withConfig (fun oldConfig => { config, oldConfig with }) <| recurseToPosition mvarId (← instantiateMVars e) stx position symm

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
  Elab.Term.withSynthesize <| withMainContext do
    let r ← (← getMainGoal).rewrite' (← getMainTarget) stx position symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

def rewriteLocalDecl' (position : List Nat) (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config) : TacticM Unit := do
    let localDecl ← fvarId.getDecl
    let rwResult ← (← getMainGoal).rewrite' localDecl.type stx position symm (config := config)
    let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
    replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)


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
  let cfg ← elabRewriteConfig stx[4]
  let loc   := expandOptLocation stx[6]
  withRWRulesSeq stx[0] stx[5] fun symm term => do
    withLocation loc
      (rewriteLocalDecl' position term symm · cfg)
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

example : ∀ (m : ℕ) n, (n = 1 ∧ True) = (1 = n ∧ True) := by
  rewriteAt [1, 1, 0, 1, 0, 1] [symm_iff]
  intro _ m
  rfl
  
example (h: ∀ n:ℕ, n = zero) : ∀ n:ℕ, n = zero := by
  rewriteAt [1,0,1] [h]
  intro _
  rfl

example (h : ∀ (m : ℕ) n, (n = 1 ∧ True) = (1 = n ∧ True)) : True := by
  rewriteAt [1, 1, 0, 1, 0, 1] [symm_iff] at h
  trivial

/- Stuff to do with the `SelectInsertPanel` -/

-- these work now :-)
example {p q : ℕ  → ℕ → Prop} (h₁ : a = b) (h₂ : ∀ q, q = p) : ∀ z : ℝ, (q b a → p a b) ∧ z = z := by
  rewriteAt [1,0,1,0,1] [h₁]
  rewriteAt [1,0,1,1,0,1] [h₁]
  rewriteAt [1,0,1,0,0,0] [h₂]
  exact λ _ ↦ ⟨id, rfl⟩

-- with ConvPanel mode
example {p q : ℕ  → ℕ → Prop} (h₁ : a = b) (h₂ : ∀ q, q = p) : ∀ z : ℝ, ∀ _ : ℚ, (q b a → p a b) ∧ z = z := by
  rewriteAt  [1,1,0,1,1,0,1] [h₁]
  rewriteAt [1,1,0,1,0,1] [h₁]
  rewriteAt [1,1,0,1,0,0,0] [h₂]
  exact λ _ _ ↦ ⟨id, rfl⟩
open Lean Meta Server

/-! # The conv? example -/

private structure SolveReturn where
  expr : Expr
  val? : Option String
  listRest : List Nat

open Lean Syntax in
def insertRewriteAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) : MetaM String := do
  let some pos := subexprPos[0]? | throwError "You must select something."
  let ⟨_, .target subexprPos⟩ := pos | throwError "You must select something in the goal."

  let mut enterval := "rewriteAt " ++ toString ((SubExpr.Pos.toArray subexprPos).toList)
  return enterval

mkSelectInsertTactic "rewriteAt?" "Select 🔍"
    "Use shift-click to select one sub-expression in the goal that you want to zoom on."
    insertRewriteAt

example (a : Nat) : a + a - a + a = a := by
  -- Put your cursor on the next line
  all_goals { sorry }
