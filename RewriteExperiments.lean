import Lean
import Mathlib
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

        if (← isDefEq lhs (e.instantiateRev fVars))
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
          throwError "subexpression '{e.instantiateRev fVars}' does not match left hand side '{lhs}' \n they have types {← inferType e} and {← inferType lhs}."

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
  
  let rec visit (e : Expr) (fVars : Array Expr) : List Nat → TacticM RewriteInfo
    | [] => matchEToLHS mvarId fVars e stx symm
    
    | ys@ (x :: xs) => do
      match x, e with
      | 0, .app f a          => let (e, e', z) ← visit f fVars xs; return (.app e a, .app e' a, z)
      | 1, .app f a          => let (e, e', z) ← visit a fVars xs; return (.app f e, .app f e', z)

      | _, .mdata d b        => let (e, e', z) ← visit b fVars ys; return (.mdata d e, .mdata d e', z)

      | 0, .proj n i b       => let (e, e', z) ← visit b fVars xs; return (.proj n i e, .proj n i e', z)

      | 0, .letE n t v b c   => let (e, e', z) ← visit t fVars xs; return (.letE n e v b c, .letE n e' v b c, z)
      | 1, .letE n t v b c   => let (e, e', z) ← visit v fVars xs; return (.letE n t e b c, .letE n t e' b c, z)
      | 2, .letE n t v b c   =>
        withLocalDeclD n (t.instantiateRev fVars) λ fVar ↦ do
        let (e, e', z) ← visit b (fVars.push fVar) xs
        return (.letE n t v e c, .letE n t v e' c, z)
                                                        
      | 0, .lam n t b bi     => let (e, e', z) ← visit t fVars xs; return (.lam n e b bi, .lam n e' b bi, z)
      | 1, .lam n t b bi     =>
        withLocalDecl n bi (t.instantiateRev fVars) λ fVar ↦ do
        let (e, e', z) ← visit b (fVars.push fVar) xs
        return (.lam n t e bi, .lam n t e' bi, z)

      | 0, .forallE n t b bi => let (e, e', z) ← visit t fVars xs; return (.forallE n e b bi, .forallE n e' b bi, z)
      | 1, .forallE n t b bi =>
        withLocalDecl n bi (t.instantiateRev fVars) λ fVar ↦ do
        let (e, e', z) ← visit b (fVars.push fVar) xs
        return (.forallE n t e bi, .forallE n t e' bi, z)

      | _, _                => throwError "could not find branch {x} in subexpression '{e}'"
      
  visit e #[] position


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
      throwTacticEx `rewriteAt mvarId "motive is not type correct"
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


