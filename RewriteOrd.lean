import Lean
import Mathlib
import SelectInsertPanel

open Function

lemma imp_left_anti (α : Prop) {β γ : Prop} : (β ≤ γ) → (γ → α) ≤ (β → α) := swap comp
lemma forall_mono (α : Sort u) {β γ : α → Prop} (f : ∀ a : α, β a ≤ γ a) : (∀ a : α, β a) ≤ (∀ a : α, γ a) := fun g y => f _ (g y)

def Pi.ndPreorder {α : Type u} {β : Type v} [Preorder β] : Preorder (α → β) where
  le f g := ∀ i, f i ≤ g i
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans

def Prop.preorder : Preorder Prop where
  le := LE.le
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans

def Prop.LE : LE Prop where
  le := LE.le


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
instance le_left_anti [Preorder α] : MonotoneClass (α := α) (. ≤ .) where
  anti := true
  order := inferInstance
  elim _ _ h _ := le_trans h

instance lt_right_mono [Preorder α] (a : α) : MonotoneClass (a < ·) where
  anti := false
  order := inferInstance
  elim _ _ := Function.swap lt_of_lt_of_le
instance lt_left_anti [Preorder α] : MonotoneClass (α := α) (· < .) where
  anti := true
  order := inferInstance
  elim _ _ h _ := lt_of_le_of_lt h

instance set_mono : MonotoneClass (α := Set α) setOf where
  anti := false
  order := inferInstance
  elim _ _ := id

instance mem_mono {a : α} : MonotoneClass (fun A : Set α => a ∈ A) where
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

@[to_additive]
instance inv_anti [OrderedCommGroup α] : MonotoneClass (fun x : α => x⁻¹) where
  anti := true
  order := inferInstance
  elim _ _ := inv_le_inv'

@[to_additive]
instance div_left_mono [OrderedCommGroup α] : MonotoneClass (· / · : α → α → α) where
  anti := false
  order := inferInstance
  elim _ _ := div_le_div_right'

@[to_additive]
instance div_right_anti [OrderedCommGroup α] {a : α}: MonotoneClass (a / · : α → α) where
  anti := true
  order := inferInstance
  elim _ _ h := div_le_div_left' h a

-- instance nat_pow_mono [Monoid M] [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (swap (· * ·)) (· ≤ ·)]
--   : MonotoneClass (fun (a : M) (n : ℕ) => (a ^ n)) where
--   anti := false
--   elim _ _ h n := pow_mono_right n h







open Lean Meta Elab.Tactic Parser.Tactic

def dependantArrowMetaTelescope
    (e : Expr) (kind : MetavarKind := MetavarKind.natural) : MetaM (Array Expr × Array BinderInfo × Expr) :=
  process #[] #[] e
where
  process (mvars : Array Expr) (bis : Array BinderInfo) (type : Expr) : MetaM (Array Expr × Array BinderInfo × Expr) := do
    match type with
    | .forallE n d b bi =>
      if b.hasLooseBVar 0
      then
        let d  := d.instantiateRev mvars
        let k  := if bi.isInstImplicit then MetavarKind.synthetic else kind
        let mvar ← mkFreshExprMVar d k n
        let mvars := mvars.push mvar
        let bis   := bis.push bi
        process mvars bis b
      else
        let type := type.instantiateRev mvars
        return (mvars, bis, type)
    | _ =>
      let type := type.instantiateRev mvars
      return (mvars, bis, type)




abbrev RewriteInfo := Expr × Expr × Array Expr × Array BinderInfo

structure OrdRewriteResult where
  eNew     : Expr
  leProof  : Expr
  mvarIds  : List MVarId


def getLEsides : Expr → MetaM (Expr × Expr)
| .app (.app _ lhs) rhs => return (lhs, rhs)
| .forallE _ lhs rhs _ => return (lhs, rhs)
| e => throwError "relation expected{indentExpr e}"

def PreordertoLE (inst : Expr) : MetaM Expr :=
  mkAppOptM `Preorder.toLE #[none, inst]

def mkLEhint (e instLE : Expr) : MetaM Expr := do
  let (lhs, rhs) ← getLEsides (← inferType e)
  let type ← mkAppOptM `LE.le #[none, instLE, lhs, rhs]
  mkExpectedTypeHint e type


def matchEToLE (mvarId : MVarId) (e preorder : Expr) (stx : Syntax) (symm : Bool) : TacticM RewriteInfo := do
  let leProof ← elabTerm stx none true
  let (newMVars, binderInfos, leTerm) ← dependantArrowMetaTelescope (← inferType leProof)
  let leProof := mkAppN leProof newMVars

  let LEinst ← PreordertoLE preorder
  let (lhs, rhs) ← getLEsides (← whnf leTerm)
  let leTerm ← mkAppOptM `LE.le #[none, LEinst, lhs, rhs]
  let newleProof ← mkExpectedTypeHint leProof leTerm

  let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
  if (← isDefEq lhs e)
    then
      -- let rhs := (← instantiateMVars rhs).instantiateRev fVars
      return (← instantiateMVars newleProof, ← instantiateMVars rhs, newMVars, binderInfos)
  else
    throwTacticEx `rewriteOrdAt mvarId m!"subexpression '{e}' does not match side '{lhs}'"



partial def recurseToPosition (mvarId : MVarId)(stx : Syntax) (symm : Bool) (position : List Nat) (e : Expr) : TacticM RewriteInfo :=
  
  let rec visit (preorder : Expr) : List Nat → Expr → TacticM RewriteInfo

    | list, .mdata d b => do let (h, e', z) ← visit preorder list b; return (h, .mdata d e', z)

    | [], e => matchEToLE mvarId e preorder stx symm
      
    | 0::xs, .app f a          => do
      let (h, e', z) ← visit (← mkAppOptM `Pi.ndPreorder #[← inferType a, none, preorder]) xs f
      return (.app h a, .app e' a, z)

    | 1::xs, .app f a          => do
      let monoClass ← mkAppOptM `MonotoneClass #[← inferType a, none, preorder, f]
      let mono ← synthInstance monoClass
      let .app (.app _ PreorderInst') monoProof ← whnfD mono | panic! "instance is not an application"
      
      let (h, e', z) ← visit PreorderInst' xs a
      return (← mkAppOptM' monoProof #[none, none, h], .app f e', z)


    -- -- | 0::xs, .proj n i b       => do let (e', z) ← visit b xs; return (.proj n i e', .proj n i e', z)

    -- -- | 0::xs, .letE n t v b c   => do let (e', z) ← visit t xs; return (.letE n e' v b c, .letE n e' v b c, z)
    -- -- | 1::xs, .letE n t v b c   => do let (e', z) ← visit v xs; return (.letE n t e' b c, .letE n t e' b c, z)
    -- -- | 2::xs, .letE n t v b c   => do
    -- --   withLocalDeclD n (t.instantiateRev) λ fVar ↦ do
    -- --   let (e', z) ← visit b xs
    -- --   return (.letE n t v e' c, .letE n t v e' c, z)
                                                      
    -- -- | 0::xs, .lam n t b bi     => do let (e', z) ← visit t xs; return (.lam n e' b bi, .lam n e' b bi, z)
    -- -- | 1::xs, .lam n t b bi     => do
    -- --   withLocalDecl n bi (t.instantiateRev) λ fVar ↦ do
    -- --   let (h, z) ← visit b anti xs
    -- --   return (.lam n t h bi, z)

    | 0::xs, .forallE n t b bi => do
      unless ← isDefEq preorder (.const `Prop.preorder []) do
        throwTacticEx `rewriteOrdAt mvarId m!"Prop is the only type with an order{indentExpr b}"
      let (h, e', z) ← visit preorder xs t
      return (← mkAppM `imp_left_anti #[b, ← mkLEhint h (.const `Prop.LE [])], .forallE n e' b bi, z)

    | 1::xs, .forallE n t b bi => do
      unless ← isDefEq preorder (.const `Prop.preorder []) do
        throwTacticEx `rewriteOrdAt mvarId m!"Prop is the only type with an order{indentExpr b}"
      withLocalDecl n bi t fun fVar => do
      let (h, e', z) ← visit preorder xs (b.instantiate1 fVar)
      return (← mkAppM `forall_mono #[t, ← mkLambdaFVars #[fVar] (← mkLEhint h (.const `Prop.LE []))], ← mkForallFVars #[fVar] e', z)

    | list, e                => throwError "could not find sub position {list} in '{repr e}'"
      
  visit (.const `Prop.preorder []) position e


def Lean.MVarId.ord_rewrite (mvarId : MVarId) (e : Expr) (stx : Syntax) (position : List Nat) (symm : Bool) (config : Rewrite.Config) : TacticM OrdRewriteResult := do
  mvarId.withContext do
    mvarId.checkNotAssigned `rewrite
    let e ← Lean.instantiateMVars e
    let (leProof, eNew, newMVars, binderInfos)
      ← withConfig (fun oldConfig => { config, oldConfig with }) <| recurseToPosition mvarId stx symm position e
    unless (← isTypeCorrect leProof) do
      throwTacticEx `rewriteOrdAt mvarId m!"the inequality proof {leProof} is not type correct"
    postprocessAppMVars `rewrite mvarId newMVars binderInfos
    let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
    let otherMVarIds ← getMVarsNoDelayed leProof
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew, leProof, mvarIds := newMVarIds.toList }


def _root_.Lean.MVarId.replaceTarget (mvarId : MVarId) (targetNew : Expr) (proof : Expr) : MetaM MVarId :=
  mvarId.withContext do
    let tag      ← mvarId.getTag
    let mvarNew  ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    let val  := .app proof mvarNew
    unless ← isTypeCorrect val do 
      throwTacticEx `rewriteOrdAt mvarId m!"target replacement does not type check{indentExpr val}"
    mvarId.assign val
    return mvarNew.mvarId!


def ord_rewriteTarget (position : List Nat) (stx : Syntax) (symm : Bool) (config : Rewrite.Config) : TacticM Unit := do
  Elab.Term.withSynthesize <| withMainContext do
    let mvarId ← getMainGoal
    let r ← mvarId.ord_rewrite (←getMainTarget) stx position symm (config := config)
    let newMvarId ← mvarId.replaceTarget r.eNew r.leProof
    
    replaceMainGoal (newMvarId :: r.mvarIds)

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
  let position := get_positions (stx[2].getArgs.toList)
  let cfg ← elabRewriteConfig stx[4]
  let loc   := expandOptLocation stx[6]
  withRWRulesSeq stx[0] stx[5] fun symm term => do
    withLocation loc
      (ord_rewriteLocalDecl position term symm · cfg)
      (ord_rewriteTarget position term symm cfg)
      (throwTacticEx `rewriteAt · "did not find instance of the pattern in the current goal")


example [Preorder α] {a b c : α} (h : b ≤ a) (g : c ≤ b) : (True → a ≤ c) → True := by
  rewriteOrdAt [0,1,0,1] [← h]
  rewriteOrdAt [0,1,1] [g]
  intro _
  trivial

-- set_option pp.explicit true
variable {α : Type u} (a : α) [Preorder α]

example {P Q : α → Prop} (h : ∀ a, P a → Q a) ( g : ∀ a, P a) : (a:α) → Q a := by
rewriteOrdAt [1] [← h]
exact g

example {A B : Set α} (h : ∀ B, A ⊆ B) (g : a ∈ A) : ∀ b : Set α, a ∈ b := by
rewriteOrdAt [1,1] [← h]
exact fun _ => g

def insertRewriteOrdAt (subexprPos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) : MetaM String := do
  let some pos := subexprPos[0]? | throwError "You must select something."
  let ⟨_, .target subexprPos⟩ := pos | throwError "You must select something in the goal."
  return "rewriteOrdAt " ++ ((SubExpr.Pos.toArray subexprPos).toList).toString

-- the rewrite button
mkSelectInsertTactic "rewriteOrdAt?" "rewriteOrdAt 🔍"
    "Use shift-click to select one sub-expression in the goal that you want to zoom on."
    insertRewriteOrdAt

