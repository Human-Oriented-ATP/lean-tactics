import Lean
import Mathlib
import Lean.Meta.ExprLens
import SelectInsertPanel

open Lean Meta Server
open Lean Meta Elab.Tactic Parser.Tactic


abbrev RewriteInfo := Expr × Expr × Expr × Expr × Array Expr × Array BinderInfo

def matchEToLHS (mvarId : MVarId) (fVars : Array Expr) (e : Expr) (stx : Syntax) (symm : Bool) : TacticM RewriteInfo := do
  let heq ← elabTerm stx none true
  let heqType ← instantiateMVars (← inferType heq)
  let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
  let heq := mkAppN heq newMVars
  let cont (heq heqType : Expr) : MetaM RewriteInfo := do
    match heqType.eq? with
    | none => throwTacticEx `rewriteAt mvarId m!"equality or iff proof expected{indentExpr heqType}"
    | some (type, lhs, rhs) =>
      let cont (heq lhs rhs : Expr) : MetaM RewriteInfo := do
        let e := e.instantiateRev fVars
        if (← isDefEq lhs e)
          then
            let mut heq ← instantiateMVars heq
            for fVar in fVars.reverse do
              heq ← mkAppM `funext #[← mkLambdaFVars #[fVar] heq]

            let rhs := (← instantiateMVars rhs).abstract fVars
            let type ← mkForallFVars fVars (← instantiateMVars type)

            let n := fVars.size
            let motive_core := (List.range n).foldr (.bvar · |> mkApp ·) (.bvar n)

            return (motive_core, rhs, heq, type, newMVars, binderInfos)
        else
          throwTacticEx `rewriteAt mvarId m!"subexpression {e} : {← inferType e} does not match left hand side {lhs} : {← inferType lhs}"

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

def recurseToPosition (mvarId : MVarId) (e : Expr) (stx : Syntax) (position : List Nat) (symm : Bool) : TacticM RewriteInfo :=
  
  let rec visit (fVars : Array Expr) : List Nat → Expr → TacticM RewriteInfo
    | list, .mdata d b         => do let (e, e', z) ← visit fVars list b; return (.mdata d e, .mdata d e', z)

    | [], e => matchEToLHS mvarId fVars e stx symm
    
    | 0::xs, .app f a          => do let (e, e', z) ← visit fVars xs f; return (.app e a, .app e' a, z)
    | 1::xs, .app f a          => do let (e, e', z) ← visit fVars xs a; return (.app f e, .app f e', z)

    | 0::xs, .proj n i b       => do let (e, e', z) ← visit fVars xs b; return (.proj n i e, .proj n i e', z)

    | 0::xs, .letE n t v b c   => do let (e, e', z) ← visit fVars xs t; return (.letE n e v b c, .letE n e' v b c, z)
    | 1::xs, .letE n t v b c   => do let (e, e', z) ← visit fVars xs v; return (.letE n t e b c, .letE n t e' b c, z)
    | 2::xs, .letE n t v b c   =>
      withLocalDeclD n (t.instantiateRev fVars) λ fVar ↦ do
        let (e, e', z) ← visit (fVars.push fVar) xs b
        return (.letE n t v e c, .letE n t v e' c, z)
                                                      
    | 0::xs, .lam n t b bi     => do let (e, e', z) ← visit fVars xs t; return (.lam n e b bi, .lam n e' b bi, z)
    | 1::xs, .lam n t b bi     =>
      withLocalDecl n bi (t.instantiateRev fVars) λ fVar ↦ do
        let (e, e', z) ← visit (fVars.push fVar) xs b
        return (.lam n t e bi, .lam n t e' bi, z)

    | 0::xs, .forallE n t b bi => do let (e, e', z) ← visit fVars xs t; return (.forallE n e b bi, .forallE n e' b bi, z)
    | 1::xs, .forallE n t b bi =>
      withLocalDecl n bi (t.instantiateRev fVars) λ fVar ↦ do
        let (e, e', z) ← visit (fVars.push fVar) xs b
        return (.forallE n t e bi, .forallE n t e' bi, z)

    | list, e                  => throwTacticEx `rewriteAt mvarId m!"could not find subexpression {list} in '{e}'"
      
  visit #[] position e


def Lean.MVarId.rewrite' (mvarId : MVarId) (e : Expr) (stx : Syntax) (position : List Nat) (symm : Bool) (config : Rewrite.Config) : TacticM RewriteResult := do
  mvarId.withContext do
    mvarId.checkNotAssigned `rewriteAt
    let e ← Lean.instantiateMVars e
    let (eAbst, eNew, heq, type, newMVars, binderInfos)
      ← withConfig (fun oldConfig => { config, oldConfig with }) <| recurseToPosition mvarId e stx position symm

    let eEqE ← mkEq e e
    let eEqEAbst := mkApp eEqE.appFn! eAbst
    let motive := Lean.mkLambda `_a BinderInfo.default type eEqEAbst
    unless (← isTypeCorrect motive) do
      throwTacticEx `rewriteAt mvarId m!"motive is not type correct{indentExpr motive}"
    let eqRefl ← mkEqRefl e
    let eqProof ← mkEqNDRec motive eqRefl heq
    -- this line changes the name of the meta variables to the form ?m.434289
    postprocessAppMVars `rewriteAt mvarId newMVars binderInfos
    let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
    let otherMVarIds ← getMVarsNoDelayed eqProof
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew, eqProof, mvarIds := newMVarIds.toList }

  
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
  let position := get_positions (stx[2].getArgs.toList)
  let cfg ← elabRewriteConfig stx[4]
  let loc   := expandOptLocation stx[6]
  withRWRulesSeq stx[0] stx[5] fun symm term => do
    withLocation loc
      (rewriteLocalDecl' position term symm · cfg)
      (rewriteTarget' position term symm cfg)
      (throwTacticEx `rewriteAt · "did not find instance of the pattern in the current goal")




example : ∀ n, n + 1 + 1 = n + 2 := by
  rewriteAt [1,0,1] [Nat.add_assoc]
  intro n
  rfl


example : ∀ (m : ℕ) n, (n = 1 ∧ True) = (1 = n ∧ True) := by
  rewriteAt [1, 1, 0, 1, 0, 1] [eq_comm]
  intro _ _
  rfl

lemma symm_iff (a b : α) : a = b ↔ b = a := eq_comm

example (α : Nat → Type u) (h : ∀ (n : Nat) (_ : α n), (n = 1 ∧ True) = (1 = n ∧ True)) : True := by
  have this := symm_iff (α := ℕ)
  specialize this ?x ?y
  rewriteAt [1, 1, 0, 1, 0, 1] [this] at h
  on_goal 3 => trivial
  exact 24236
  exact 5432



example {p q : ℕ  → ℕ → Prop} {α : ℝ → Type u} (h₁ : a = b) (h₂ : ∀ q, q = p) : ∀ z : ℝ, ∀ _ : α z, (q b a → p a b) ∧ z = z := by
  rewriteAt  [1,1,0,1,1,0,1] [h₁]
  rewriteAt [1,1,0,1,0,1] [h₁]
  rewriteAt [1,1,0,1,0,0,0] [h₂]
  exact λ _ _ ↦ ⟨id, rfl⟩

syntax binderIdent "•" : term

macro_rules
| `($h:ident •) => `(?$h)
| `($h:hole •) => `(?$h)
  
example : 0 = (0: ℝ)  ∧ 0 = 1-(1 : ℤ) ∧ 0 = 1-(1 : ℤ)  := by
refine ⟨ l•, r•⟩ 
on_goal 1 =>
  rewriteAt [0,1] [← sub_self]
  rewriteAt [1] [← sub_self]
on_goal 5 =>
  constructor
  on_goal 2 => rewriteAt [0,1] [← sub_self (G := ℤ )]
  on_goal 1 => rewriteAt [0,1] [← sub_self (G := ℤ )]
  rfl
  rfl
rfl
exact 100

def insertRewriteAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) : MetaM String := do
  let some pos := subexprPos[0]? | throwError "You must select something."
  let ⟨_, .target subexprPos⟩ := pos | throwError "You must select something in the goal."
  return "rewriteAt " ++ ((SubExpr.Pos.toArray subexprPos).toList).toString

-- the rewrite button
mkSelectInsertTactic "rewriteAt?" "rewriteAt 🔍"
    "Use shift-click to select one sub-expression in the goal that you want to zoom on."
    insertRewriteAt

--try the tactic-out below 
example : 0 = (0: ℝ)  ∧ 0 = 1-(1 : ℤ) ∧ 0 = 1-(1 : ℤ) := by sorry

