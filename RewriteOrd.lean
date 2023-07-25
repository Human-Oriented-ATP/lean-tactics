import Lean
import Mathlib

open Function

lemma imp_left_anti (x : Prop) {a b : Prop} : (a → b) → (b → x) → (a → x) := swap comp
lemma imp_right_mono (x : Prop) {a b : Prop} : (a → b) → (x → a) → (x → b) := comp

def Pi.ndPreorder {α : Type u} {β : Type v} [Preorder β] : Preorder (α → β) where
  le f g := ∀ i, f i ≤ g i
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans

def Prop.preorder : Preorder Prop where
  le := LE.le
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans



class MonotoneClass {α : Type u} {β : Type v} [Preorder β] (f : α → β) where
  anti : Bool
  order : Preorder α
  elim : if anti then @Antitone _ _ order _ f else @Monotone _ _ order _ f


instance or_right_mono {P : Prop} : MonotoneClass (Or P) where
  anti := false
  order := inferInstance
  elim _ _ := Or.imp_right
instance or_left_mono : MonotoneClass Or where
  anti := false
  order := inferInstance
  elim _ _ h _ := Or.imp_left h

instance and_right_mono {P : Prop} : MonotoneClass (And P) where
  anti := false
  order := inferInstance
  elim _ _ := And.imp_right
instance and_left_mono : MonotoneClass And where
  anti := false
  order := inferInstance
  elim _ _ h _ := And.imp_left h

instance le_right_mono [Preorder α] (a : α) : MonotoneClass (a ≤ ·) where
  anti := false
  order := inferInstance
  elim _ _ := Function.swap le_trans
instance le_left_anti [Preorder α] : MonotoneClass (α := α) LE.le where
  anti := true
  order := inferInstance
  elim _ _ h _ := le_trans h

instance lt_right_mono [Preorder α] (a : α) : MonotoneClass (a < ·) where
  anti := false
  order := inferInstance
  elim _ _ := Function.swap lt_of_lt_of_le
instance lt_left_anti [Preorder α] : MonotoneClass (α := α) LT.lt where
  anti := true
  order := inferInstance
  elim _ _ h _ := lt_of_le_of_lt h

instance set_mono : MonotoneClass (α := Set α) setOf where
  anti := false
  order := inferInstance
  elim _ _ := id
instance elem_mono {a : α} : MonotoneClass (Set.Mem a) where
  anti := false
  order := inferInstance
  elim _ _ sub mem := sub mem

instance add_left_mono {μ : α → β → α} [Preorder α] [i : CovariantClass β α (swap μ) (· ≤ ·)] : MonotoneClass μ where
  anti := false
  order := inferInstance
  elim _ _ h b := i.elim b h
instance add_right_mono {μ : β → α → α} [Preorder α] [i : CovariantClass β α μ (· ≤ ·)] {a : β} : MonotoneClass (μ a) where
  anti := false
  order := inferInstance
  elim _ _ := i.elim a

-- instance nat_pow_mono [Monoid M] [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (swap (· * ·)) (· ≤ ·)]
--   : MonotoneClass (fun (a : M) (n : ℕ) => (a ^ n)) where
--   anti := false
--   elim _ _ h n := pow_mono_right n h







open Lean Meta Elab.Tactic Parser.Tactic

abbrev RewriteInfo := Expr × Expr × Array Expr × Array BinderInfo

structure OrdRewriteResult where
  eNew     : Expr
  leProof  : Expr
  mvarIds  : List MVarId


def matchEToLE (mvarId : MVarId) (fVars : Array Expr) (e : Expr) (stx : Syntax) (symm : Bool) : TacticM RewriteInfo := do
  let hle ← elabTerm stx none true
  let hleType ← instantiateMVars (← inferType hle)
  let (newMVars, binderInfos, hleType) ← forallMetaTelescopeReducing hleType
  let hle := mkAppN hle newMVars
  match Expr.app4? hleType ``LE.le with
  | none => throwTacticEx `rewrite mvarId m!"(· ≤ ·) proof expected{indentExpr hleType}"
  | some (_type, _inst, lhs, rhs) =>
    let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)

    if (← isDefEq lhs (e.instantiateRev fVars))
      then
        return ((← instantiateMVars hle).abstract fVars, ← instantiateMVars rhs, newMVars, binderInfos)
    else
      throwError "subexpression '{e.instantiateRev fVars}' does not match side '{if symm then rhs else lhs}'"


def recurseToPosition (mvarId : MVarId) (e : Expr) (stx : Syntax) (position : List Nat) (symm : Bool) : TacticM RewriteInfo :=
  
  let rec visit (e preorderInst : Expr) (fVars : Array Expr) : List Nat → TacticM RewriteInfo
    | [] => matchEToLE mvarId fVars e stx symm
    
    | ys@ (x :: xs) => do
      match x, e with
      
      | 0, .app f a          =>
        let (h, e', z) ← visit f (← mkAppOptM `Pi.ndPreorder #[← inferType a, none, preorderInst]) fVars xs
        return (.app h a, .app e' a, z)

      | 1, .app f a          =>
        let monoClass ← mkAppOptM `MonotoneClass #[← inferType a, none, preorderInst, f]
        let mono ← synthInstance monoClass
        let .app (.app _ PreorderInst') monoProof ← whnfD mono | panic! "instance is not an application"
        
        let (h, e', z) ← visit a PreorderInst' fVars xs
        return (← mkAppOptM' monoProof #[none, none, h], .app f e', z)


      | _, .mdata d b        => let (h, e', z) ← visit b preorderInst fVars ys; return (h, .mdata d e', z)

      -- -- | 0, .proj n i b       => let (e', z) ← visit b fVars xs; return (.proj n i e', .proj n i e', z)

      -- -- | 0, .letE n t v b c   => let (e', z) ← visit t fVars xs; return (.letE n e' v b c, .letE n e' v b c, z)
      -- -- | 1, .letE n t v b c   => let (e', z) ← visit v fVars xs; return (.letE n t e' b c, .letE n t e' b c, z)
      -- -- | 2, .letE n t v b c   =>
      -- --   withLocalDeclD n (t.instantiateRev fVars) λ fVar ↦ do
      -- --   let (e', z) ← visit b (fVars.push fVar) xs
      -- --   return (.letE n t v e' c, .letE n t v e' c, z)
                                                        
      -- -- | 0, .lam n t b bi     => let (e', z) ← visit t fVars xs; return (.lam n e' b bi, .lam n e' b bi, z)
      -- -- | 1, .lam n t b bi     =>
      -- --   withLocalDecl n bi (t.instantiateRev fVars) λ fVar ↦ do
      -- --   let (h, z) ← visit b (fVars.push fVar) anti xs
      -- --   return (.lam n t h bi, z)

      | 0, .forallE n t b bi =>
        unless ← isDefEq preorderInst (.const `Prop.preorder []) do
          throwError "There is no order on types other than Prop{indentExpr b}"
        let (h, e', z) ← visit t preorderInst fVars xs
        return (← mkAppM `imp_left_anti #[b,h], .forallE n e' b bi, z)
      | 1, .forallE n t b bi =>
        unless ← isDefEq preorderInst (.const `Prop.preorder []) do
          throwError "There is no order on types other than Prop{indentExpr b}"
        let (h, e', z) ← visit b preorderInst fVars xs
        return (← mkAppM `imp_right_mono #[t,h], .forallE n t e' bi, z)
      | _, _                => throwError "could not find branch {x} in subexpression '{repr e}'"
      
  visit e (.const `Prop.preorder []) #[] position


def Lean.MVarId.ord_rewrite (mvarId : MVarId) (e : Expr) (stx : Syntax) (position : List Nat) (symm : Bool) (config : Rewrite.Config) : TacticM OrdRewriteResult := do
  mvarId.withContext do
    mvarId.checkNotAssigned `rewrite
    let e ← Lean.instantiateMVars e
    let (leProof, eNew, newMVars, binderInfos)
      ← withConfig (fun oldConfig => { config, oldConfig with }) <| recurseToPosition mvarId e stx position symm
    unless (← isTypeCorrect leProof) do
      throwTacticEx `rewrite mvarId "the inequality proof is not type correct"
    postprocessAppMVars `rewrite mvarId newMVars binderInfos
    let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
    let otherMVarIds ← getMVarsNoDelayed leProof
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew, leProof, mvarIds := newMVarIds.toList }


def ord_rewriteTarget (position : List Nat) (stx : Syntax) (symm : Bool) (config : Rewrite.Config) : TacticM Unit := do
  Elab.Term.withSynthesize <| withMainContext do
    let mvarId ← getMainGoal
    let r ← (← getMainGoal).ord_rewrite (←getMainTarget) stx position symm (config := config)
    let mvarNew  ← mkFreshExprMVar r.eNew MetavarKind.syntheticOpaque
    
    let val := .app r.leProof mvarNew
    unless ← isTypeCorrect val do
      throwTacticEx `rewrite mvarId "the inequality proof does not apply"
    mvarId.assign val
    
    replaceMainGoal (mvarNew.mvarId! :: r.mvarIds)

def ord_rewriteLocalDecl (position : List Nat) (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config) : TacticM Unit := pure ()
    -- let localDecl ← fvarId.getDecl
    -- let rwResult ← (← getMainGoal).ord_rewrite localDecl.type stx position symm (config := config)
    -- let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
    -- replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)


def get_positions : List Syntax → List Nat
| [] => []
| x :: xs =>
  let rec go : List Syntax → List Nat
    | [] => []
    | _ :: y :: ys => TSyntax.getNat ⟨y⟩ :: go ys
    | _ => panic! "even length nonempy list"
  TSyntax.getNat ⟨x⟩ :: go xs

syntax (name := orewriteSeq') "rewriteOrdAt" "[" num,* "]" (config)? rwRuleSeq (location)? : tactic

@[tactic orewriteSeq'] def evalOrdRewriteSeq : Tactic := fun stx => do
  let list := (stx[2].getArgs.toList)
  unless List.length list % 2 == 1 do
    throwTacticEx `rewriteAt (← getMainGoal)  m!"even length list"
  let position := get_positions (stx[2].getArgs.toList)
  let cfg ← elabRewriteConfig stx[4]
  let loc   := expandOptLocation stx[6]
  withRWRulesSeq stx[0] stx[5] fun symm term => do
    withLocation loc
      (ord_rewriteLocalDecl position term symm · cfg)
      (ord_rewriteTarget position term symm cfg)
      (throwTacticEx `rewriteAt · "did not find instance of the pattern in the current goal")




example [Preorder α] {a b c : α} (h : b ≤ a) (g : b ≤ c) : (True → a ≤ c) → True := by
rewriteOrdAt [0,1,0,1] [← h]
intro _
trivial

