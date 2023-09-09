import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Data.SetLike.Basic
import TreeApply
import TreeRewrite
import Mathlib.Algebra.Order.Group.Defs


open Function

class MonotoneClass {α : Type u} {β : Type v} [Preorder β] (f : α → β) where
  anti : Bool
  order : Preorder α
  elim : if anti then @Antitone _ _ order _ f else @Monotone _ _ order _ f


instance or_right_mono {P : Prop} : MonotoneClass (Or P) where
  anti := false
  elim _ _ := Or.imp_right
instance or_left_mono : MonotoneClass Or where
  anti := false
  elim _ _ h _ := Or.imp_left h

instance and_right_mono {P : Prop} : MonotoneClass (And P) where
  anti := false
  elim _ _ := And.imp_right
instance and_left_mono : MonotoneClass And where
  anti := false
  elim _ _ h _ := And.imp_left h

instance exists_mono {α : Type u} : MonotoneClass (@_root_.Exists α) where
  anti := false
  elim _ _ := Exists.imp
    

instance le_right_mono [Preorder α] (a : α) : MonotoneClass (a ≤ ·) where
  anti := false
  elim _ _ := swap le_trans
instance le_left_anti [Preorder α] : MonotoneClass (α := α) (. ≤ .) where
  anti := true
  elim _ _ h _ := le_trans h

instance imp_right_mono (a : Prop) : MonotoneClass (Tree.Imp a) := le_right_mono a
instance imp_left_anti : MonotoneClass Tree.Imp := le_left_anti

instance sub_right_mono (a : Set α) : MonotoneClass (a ⊆ ·) := le_right_mono a
instance sub_left_anti : MonotoneClass (α := Set α) (. ⊆ .) := le_left_anti 

instance lt_right_mono [Preorder α] (a : α) : MonotoneClass (a < ·) where
  anti := false
  elim _ _ := swap lt_of_lt_of_le
instance lt_left_anti [Preorder α] : MonotoneClass (α := α) (· < .) where
  anti := true
  elim _ _ h _ := lt_of_le_of_lt h

instance ssub_right_mono (a : Set α) : MonotoneClass (a ⊂ ·) := lt_right_mono a
instance ssub_left_anti : MonotoneClass (α := Set α) (. ⊂ .) := lt_left_anti 

instance set_mono : MonotoneClass (@setOf α) where
  anti := false
  elim _ _ := id

instance mem_mono {a : α} : MonotoneClass (fun A : Set α => a ∈ A) where
  anti := false
  elim _ _ sub mem := Set.mem_of_subset_of_mem sub mem

instance add_left_mono {μ : α → β → α} [Preorder α] [i : CovariantClass β α (swap μ) (· ≤ ·)] : MonotoneClass μ where
  anti := false
  elim _ _ h b := i.elim b h

instance add_right_mono {μ : β → α → α} [Preorder α] [i : CovariantClass β α μ (· ≤ ·)] {a : β} : MonotoneClass (μ a) where
  anti := false
  elim _ _ := i.elim a

@[to_additive]
instance inv_anti [OrderedCommGroup α] : MonotoneClass (fun x : α => x⁻¹) where
  anti := true
  elim _ _ := inv_le_inv'

@[to_additive]
instance div_left_mono [OrderedCommGroup α] : MonotoneClass (· / · : α → α → α) where
  anti := false
  elim _ _ := div_le_div_right'

@[to_additive]
instance div_right_anti [OrderedCommGroup α] {a : α} : MonotoneClass (a / · : α → α) where
  anti := true
  elim _ _ h := div_le_div_left' h a

-- instance nat_pow_mono [Monoid M] [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (swap (· * ·)) (· ≤ ·)]
--   : MonotoneClass (fun (a : M) (n : ℕ) => (a ^ n)) where
--   anti := false
--   elim _ _ h n := pow_mono_right n h



namespace Tree



open Lean Meta


abbrev RewriteOrdInfo := Expr × Expr

-- def PreordertoLE (u : Level) (α inst : Expr) : Expr :=
--   mkApp2 (.const ``Preorder.toLE [u]) α inst

-- def PreordertoLT (u : Level) (α inst : Expr) : Expr :=
--   mkApp2 (.const ``Preorder.toLT [u]) α inst

def mkLE (u : Level) (α preorder : Expr) : Expr :=
  mkApp2 (.const ``LE.le [u]) α (mkApp2 (.const ``Preorder.toLE [u]) α preorder)

def mkLT (u : Level) (α preorder : Expr) : Expr :=
  mkApp2 (.const ``LT.lt [u]) α (mkApp2 (.const ``Preorder.toLT [u]) α preorder)
def Prop.preorder : Preorder Prop where
  le := LE.le
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans

private inductive Pattern where
  | le
  | lt
  | imp
deriving BEq

def getLEsides (u : Level) (rel α preorder target : Expr) : MetaM (Pattern × Expr × Expr) := do
  match rel with
    | .app (.app r lhs) rhs => do
      if ← isDefEq r (mkLE u α preorder) then
        return (.le, lhs, rhs)

      if ← isDefEq r (mkLT u α preorder) then
        return (.lt, lhs, rhs)

      throwError m! "expected an inequality for {target} : {α}, not {indentExpr rel}"
    
    | .forallE _ lhs rhs _ => do
      if rhs.hasLooseBVars then
        throwError m! "expected an inequality for {target} : {α}, not {indentExpr rel}" 
      if ← isDefEq preorder (.const ``Prop.preorder []) then
        return (.imp, lhs, rhs)

      throwError m! "expected an inequality for {target} : {α}, not {indentExpr rel}"

    | _ => throwError m! "expected an inequality for {target} : {α}, not {indentExpr rel}"


def getLEsides! : Pattern → Expr → Expr × Expr
  | .imp, .forallE _ lhs rhs _  => (lhs, rhs)
  | _   , .app (.app _ lhs) rhs => (lhs, rhs)
  | _, _ => panic! ""

def rewriteOrdUnify (fvars : Array Expr) (u : Level) (α preorder rel target : Expr) (hypContext : HypothesisContext) (pol : Bool) : MetaM' RewriteOrdInfo := do
  let {metaIntro, instMetaIntro, hypProofM} := hypContext
  let mvars ← metaIntro
  let instMVars ← instMetaIntro

  let (pattern, lhs, rhs) ← getLEsides u rel α preorder target
  let side := if pol then rhs else lhs

  if (← isDefEq side target)
  then
    synthMetaInstances instMVars
    for mvar in mvars do
      _ ← elimMVarDeps fvars mvar

    let (newRel, proof) ← hypProofM
    let (lhs, rhs) := getLEsides! pattern newRel
    if pattern != .lt
    then
      let newRel := mkApp2 (mkLE u α preorder) lhs rhs
      let proof := mkApp2 (mkConst ``id [.zero]) newRel proof
      return (if pol then lhs else rhs, proof)
    else
      let proof := mkApp5 (.const ``le_of_lt [u]) α preorder lhs rhs proof
      return (if pol then lhs else rhs, proof)
  else
    throwError m!"subexpression '{target}' does not match side '{side}'"



lemma imp_left_anti' (α : Prop) {β γ : Prop} : (β ≤ γ) → (γ → α) ≤ (β → α) := swap comp
lemma forall_mono (α : Sort u) {β γ : α → Prop} (h : ∀ a, β a ≤ γ a) : (∀ a, β a) ≤ (∀ a, γ a) := fun g y => h _ (g y)

lemma funext_ord {α : Type u} {β : Type v} [Preorder β] {f g : α → β} (h : ∀ a, f a ≤ g a) : f ≤ g := by exact h

def Pi.ndPreorder {α : Type u} {β : Type v} [Preorder β] : Preorder (α → β) := Pi.preorder



def Prop.LE : LE Prop where
  le := LE.le

partial def treeRewriteOrd (rel : Expr) (hypContext : HypothesisContext) (pos : List Nat) (pol : Bool) (target : Expr) : MetaM' TreeProof := do
  
  let rec visit (u : Level) (α preorder : Expr) (fvars : Array Expr) (pol : Bool) : List Nat → Expr → MetaM' RewriteOrdInfo
    -- write lhs for the original subexpressiont, and rhs for the replaced subexpression
    | xs, .mdata d lhs => do
      let (rhs, h) ← visit u α preorder fvars pol xs lhs
      return (.mdata d rhs, h)

    | [], lhs => rewriteOrdUnify fvars u α preorder rel lhs hypContext pol
      
    | 0::xs, .app lhs a => do
      let α' ← inferType a
      let v ← getDecLevel α'
      let uNew := (Level.imax v u).normalize
      let (rhs, h) ← visit uNew (.forallE `_a α' α .default) (mkApp3 (.const ``Pi.ndPreorder [v, u]) α' α preorder) fvars pol xs lhs
      return (.app rhs a, .app h a)

    | 1::xs, .app f lhs => do
      let typeNew ← inferType lhs
      let uNew ← getDecLevel typeNew
      let monoClass := mkApp4 (.const ``MonotoneClass [uNew, u]) typeNew α preorder f
      let mono ← synthInstance monoClass
      let .app (.app (.app _ anti) preorder') monoProof ← whnfD mono | panic! "instance is not an application"
      let anti ← match anti with
        | .const ``true  [] => pure true
        | .const ``false [] => pure false
        | _ => throwError m! "Boolean value not known: {indentExpr anti}"
      
      let (rhs, h) ← visit uNew typeNew preorder' fvars (pol != anti) xs lhs
      return (.app f rhs, ← mkAppOptM' monoProof #[none, none, h])


    | 2::xs, .letE n t v lhs d => do 
      withLocalDeclD n (t.instantiateRev fvars) fun fvar => do
      let (rhs, h) ← visit u α preorder (fvars.push fvar) pol xs (lhs.instantiate1 fvar)
      
      return (.letE n t v (rhs.abstract #[fvar]) d, .letE n t v (h.abstract #[fvar]) d)

                                                      
    | 1::xs, .lam n t lhs bi => do
      withLocalDecl n bi (t.instantiateRev fvars) fun fvar => do
      let .forallE _ α' β _ := α | panic! "type of lambda is not a forall"
      let u ← getDecLevel α'
      let v ← getDecLevel β 
      let newPreorder ← mkFreshExprMVar (mkApp (.const ``Preorder [v]) β)
      let requiredPreorder := mkApp3 (.const ``Pi.ndPreorder [u, v]) α' β newPreorder
      unless ← isDefEq preorder requiredPreorder do
        throwError m! "Preorder on lambda is not a Pi.Preorder, {preorder}, {requiredPreorder}"

      let (rhs, h) ← visit v β (← instantiateMVars newPreorder) (fvars.push fvar) pol xs (lhs.instantiate1 fvar)
      return (.lam n t (rhs.abstract #[fvar]) bi, .lam n t (h.abstract #[fvar]) bi)


    | 0::xs, .forallE n lhs b bi => do
      unless ← isDefEq preorder (.const ``Prop.preorder []) do
        throwError m!"Prop is the only type with an order{indentExpr b}"
      let (rhs, h) ← visit u α preorder fvars (!pol) xs lhs
      let h   := mkApp2 (mkConst ``id [.zero]) ((if pol then id else swap) (mkApp2 (mkLE u α preorder)) lhs rhs) h
      return (.forallE n rhs b bi, mkApp ((if pol then id else swap) (mkApp3 (.const ``imp_left_anti' []) b) lhs rhs) h)

    | 1::xs, .forallE n t lhs bi => do
      unless ← isDefEq preorder (.const ``Prop.preorder []) do
        throwError m!"Prop is the only type with an order{indentExpr lhs}"

      withLocalDecl n bi (t.instantiateRev fvars) fun fvar => do
      let (rhs, h) ← visit u α preorder (fvars.push fvar) pol xs (lhs.instantiate1 fvar)
      let h   := mkApp2 (mkConst ``id [.zero]) ((if pol then swap else id) (mkApp2 (mkLE u α preorder)) lhs rhs) h
      let h   := .lam n t (h.abstract #[fvar]) bi
      
      let lhs := .lam n t (lhs.abstract #[fvar]) bi
      let rhs := rhs.abstract #[fvar]
      let (rhs, rhs') := (.forallE n t rhs bi, .lam n t rhs bi)
      
      return (rhs, mkApp ((if pol then swap else id) (mkApp3 (.const  ``forall_mono [← getLevel t]) t) lhs rhs') h)

    | list, lhs => throwError "could not find sub position {list} in '{repr lhs}'"
      
  let (newTree, proof) ← visit (.zero) (.sort .zero) (.const ``Prop.preorder []) #[] pol pos target
  return { newTree, proof}



open Elab.Tactic

syntax (name := tree_rewrite_ord) "tree_rewrite_ord" treePos treePos : tactic

@[tactic tree_rewrite_ord]
def evalTreeRewriteOrd : Tactic := fun stx => do
  let hypPos := get_positions stx[1]
  let goalPos := get_positions stx[2]
  workOnTree (applyBound hypPos goalPos · true (treeRewriteOrd))


syntax (name := lib_rewrite_ord) "lib_rewrite_ord" ident treePos : tactic

@[tactic lib_rewrite_ord]
def evalLibRewriteOrd : Tactic := fun stx => do
  let hypPos := stx[1].getId
  let goalPos := get_positions stx[2]
  workOnTree (applyUnbound hypPos goalPos · treeRewriteOrd)





example : [PseudoMetricSpace α] → [PseudoMetricSpace β] → (f : α → β)
  → UniformContinuous f → Continuous f := by
  make_tree
  lib_rewrite Metric.uniformContinuous_iff [1,1,1,1,1,1,0,1]
  lib_rewrite Metric.continuous_iff [1,1,1,1,1,1,1]
  tree_apply [1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,0,1] [1,1,1,0,1]
  tree_apply [1,1,0,1] [1,1,1]


lemma exists_mem_Ioo (a b : ℝ) (h : a < b) : ∃ x, x ∈ Set.Ioo a b :=
  ⟨(a + b) / 2, ⟨by linarith, by linarith⟩⟩


example [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β)
  : LipschitzWith 1 f → Continuous f := by
  make_tree
  lib_rewrite Metric.continuous_iff [1]
  lib_rewrite lipschitzWith_iff_dist_le_mul [0,1]
  norm_num
  tree_rewrite_ord [0,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,0,1]
  tree_rewrite_ord [1,1,1,1,1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1,1,1,1,1,0,1]
  lib_rewrite_rev Set.mem_Ioo [1,1,1,1,1]
  lib_apply Tree.exists_mem_Ioo [1,1,1,1,1]
  tree_apply [1,1,0,1] [1,1,1]




example : (0 ≤ 1) → 0 ≤ 1 := by
  make_tree
  tree_rewrite_ord [0,1] [1,0,1]
  rfl

example (p q : Prop) : (p → q) → True ∨ (p → q) := by
  make_tree
  tree_rewrite_ord [0,1] [1,1,1]
  sorry

example (p q : Prop) : Imp (p → q) <| True ∨ (p → q) := by
  tree_rewrite_ord [0,1] [1,1,1]
  sorry

example (p q : Prop) : Imp (p → q) <| True ∨ (p → q) := by
  tree_rewrite_ord [0,1] [1,1,0]
  sorry

example (𝔸 : Set (Set α)) (B C : Set α) : (C ⊆ B) → {A ∈ 𝔸 | B ⊂ A} ⊆ {A ∈ 𝔸 | C ⊂ A} := by
  make_tree
  tree_rewrite_ord [0,1] [1,0,1,1,1,1,0,1]
  rfl

example : (∀ x, x - 1 ≤ x) → {x : Nat | x ≤ 4 } ⊆ {x : Nat | x - 1 ≤ 4} := by
  make_tree
  tree_rewrite_ord [0,1,1,1] [1,0,1,1,1,0,1]
  rfl

example : Imp (Forall ℕ fun x => x - 1 ≤ x) <| ∃ n, n - 1 ≤ n := by
  tree_rewrite_ord [0,1,1,1] [1,1,1,1]
  use 0    

example : Imp (Forall ℕ fun x => x - 1 ≤ x) <| ∀ n, n - 1 ≤ n := by
  tree_rewrite_ord [0,1,1,1] [1,1,1]
  make_tree
  lib_apply refl [1,1]

/-
What should the isolate tactic do?

For existence problems, we like to isolate the variable in an equality, for example
· x + 1 = 2 => x = 2 - 1
· 4 / x = 2 => x = 4 / 2 (with side condition that 2 and x are non-zero)

So in general, we have a function with an argument on one side, and something on the other side:
f a = b

which turns into
a = f⁻¹ b

Maybe the function is not fully invertible, but only under some hypothesis, e.g. a and b are nonzero.
Ah, so then this is just a form of finding the library result, and applying it.

-/

