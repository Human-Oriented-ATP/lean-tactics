import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Data.SetLike.Basic
import TreeApply
import Mathlib.Algebra.Order.Group.Defs

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





namespace Tree


open Lean Meta Elab.Tactic Parser.Tactic


abbrev RewriteOrdInfo := Expr × Expr


structure OrdRewriteResult where
  eNew     : Expr
  leProof  : Expr
  mvarIds  : List MVarId


def getLEsides [Monad m] [MonadError m] : Expr → m (Expr × Expr)
| .app (.app _ lhs) rhs => return (lhs, rhs)
| .forallE _ lhs rhs _ => return (lhs, rhs)
| e => throwError "relation expected{indentExpr e}"

def PreordertoLE (inst : Expr) : MetaM Expr :=
  mkAppOptM ``Preorder.toLE #[none, inst]

def mkLEhint (e instLE : Expr) : MetaM Expr := do
  let (lhs, rhs) ← getLEsides (← inferType e)
  let type ← mkAppOptM ``LE.le #[none, instLE, lhs, rhs]
  mkExpectedTypeHint e type


def matchEToLE (fvars : Array Expr) (rel target type preorder : Expr) (metaIntro : MetaM (Array Expr)) (proofM : MetaM' (Expr × Expr)) (pol : Bool) : MetaM' RewriteOrdInfo := do

  let le ← PreordertoLE preorder
  let side := (if pol then Prod.snd else Prod.fst) (← getLEsides rel)
  _ ← metaIntro
  if (← isDefEq side target)
  then
    let (newRel, proof) ← proofM
    let (lhs, rhs) ← getLEsides newRel
    let newRel ← mkAppOptM ``LE.le #[type, le, lhs, rhs]
    -- logInfo m! "{lhs}, {rhs}, {type}, {le}, {preorder}"
    let proof ← mkExpectedTypeHint proof newRel
    return (if pol then lhs else rhs, proof)
  else
    throwError m!"subexpression '{target}' does not match side '{side}'"



partial def recurseToPosition (rel : Expr) (metaIntro : MetaM (Array Expr)) (proofM : MetaM' (Expr × Expr)) (position : List Nat) (pol : Bool) (e : Expr) : MetaM' RewriteOrdInfo :=
  
  let rec visit (u : Level) (type preorder : Expr) (fvars : Array Expr) (pol : Bool) : List Nat → Expr → MetaM' RewriteOrdInfo

    | xs, .mdata d b => do let (e, h) ← visit u type preorder fvars pol xs b; return (.mdata d e, h)

    | [], e => matchEToLE fvars rel e type preorder metaIntro proofM pol
      
    | 0::xs, .app f a          => do
      let α ← inferType a
      let v ← getDecLevel α
      let uNew := (Level.imax v u).normalize
      let (e, h) ← visit uNew (.forallE `_a α type .default) (mkApp3 (.const ``Pi.ndPreorder [v, u]) α type preorder) fvars pol xs f
      return (.app e a, .app h a)

    | 1::xs, .app f a          => do
      let typeNew ← inferType a
      let uNew ← getDecLevel typeNew
      logInfo m!"{type}, {u}"
      let monoClass := mkApp4 (.const ``MonotoneClass [uNew, u]) typeNew type preorder f
      let mono ← synthInstance monoClass
      let .app (.app (.app _ anti) preorder') monoProof ← whnfD mono | panic! "instance is not an application"
      let anti := match anti with
        | .const ``true [] => true
        | .const ``false [] => false
        | _ => panic! "polarity not known"
      
      
      let (e, h) ← visit uNew typeNew preorder' fvars (pol != anti) xs a
      return (.app f e, ← mkAppOptM' monoProof #[none, none, h])


    -- -- | 0::xs, .letE n t v b c   => do let (e) ← visit t xs; return (.letE n e v b c, .letE n e v b c)
    -- -- | 1::xs, .letE n t v b c   => do let (e) ← visit v xs; return (.letE n t e b c, .letE n t e b c)
    -- -- | 2::xs, .letE n t v b c   => do
    -- --   withLocalDeclD n (t.instantiateRev) λ fvar ↦ do
    -- --   let (e) ← visit b xs
    -- --   return (.letE n t v e c, .letE n t v e c)
                                                      
    -- -- | 0::xs, .lam n t b bi     => do let (e) ← visit t xs; return (.lam n e b bi, .lam n e b bi)
    -- -- | 1::xs, .lam n t b bi     => do
    -- --   withLocalDecl n bi (t.instantiateRev) λ fvar ↦ do
    -- --   let (h) ← visit b anti xs
    -- --   return (.lam n t h bi)

    | 0::xs, .forallE n t b bi => do
      unless ← isDefEq preorder (.const ``Prop.preorder []) do
        throwError m!"Prop is the only type with an order{indentExpr b}"
      let (e, h) ← visit u type preorder fvars (!pol) xs t
      return (.forallE n e b bi, ← mkAppM ``imp_left_anti #[b, ← mkLEhint h (.const `Prop.LE [])])

    | 1::xs, .forallE n t b bi => do
      unless ← isDefEq preorder (.const ``Prop.preorder []) do
        throwError m!"Prop is the only type with an order{indentExpr b}"
      withLocalDecl n bi t fun fvar => do
      let (e, h) ← visit u type preorder fvars pol xs (b.instantiate1 fvar)
      return (← mkForallFVars #[fvar] e, ← mkAppM ``forall_mono #[t, ← mkLambdaFVars #[fvar] (← mkLEhint h (.const `Prop.LE []))])

    | list, e                => throwError "could not find sub position {list} in '{repr e}'"
      
  visit (.zero) (.sort .zero) (.const ``Prop.preorder []) #[] pol position e





def treeRewriteOrd (rel : Expr) (metaIntro : MetaM (Array Expr)) (proofM : MetaM' (Expr × Expr)) (pos : List Nat) (pol : Bool) (target : Expr) : MetaM' TreeProof := do
  let (newSide, proof) ← recurseToPosition rel metaIntro proofM pos pol target
  return { newTree := newSide, proof}



open Elab Tactic

syntax (name := tree_rewrite_ord) "tree_rewrite_ord" treePos treePos : tactic

@[tactic tree_rewrite_ord]
def evalTreeRewriteOrd : Tactic := fun stx => do
  let hypPos := get_positions stx[1]
  let goalPos := get_positions stx[2]
  workOnTree (applyBound hypPos goalPos · true (treeRewriteOrd))

-- set_option pp.all true
example : (0 ≤ 1) → 0 ≤ 1 := by
  make_tree
  tree_rewrite_ord [0,1] [1,0,1]
  rfl

example (p q : Prop) : (p → q) → True ∨ (p → q) := by
  make_tree
  tree_rewrite_ord [0,1] [1,1,0]
  sorry