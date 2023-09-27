import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Order.Group.Defs
import TreeMoves.TreeApply
import Mathlib.Topology.MetricSpace.Basic

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

instance tree_and_right_mono {P : Prop} : MonotoneClass (Tree.And P) := and_right_mono
instance tree_and_left_mono : MonotoneClass Tree.And := and_left_mono

instance exists_mono {α : Type u} : MonotoneClass (@_root_.Exists α) where
  anti := false
  elim _ _ := Exists.imp
    

instance le_right_mono [Preorder α] (a : α) : MonotoneClass (a ≤ ·) where
  anti := false
  elim _ _ := swap le_trans
instance le_left_anti [Preorder α] : MonotoneClass (α := α) (. ≤ .) where
  anti := true
  elim _ _ h _ := le_trans h

instance imp_right_mono (a : Prop) : MonotoneClass (a → ·) := le_right_mono a
instance imp_left_anti : MonotoneClass (· → ·) := le_left_anti

instance tree_imp_right_mono (a : Prop) : MonotoneClass (Tree.Imp a) := le_right_mono a
instance Tree_imp_left_anti : MonotoneClass Tree.Imp := le_left_anti

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


def mkLE (u : Level) (α preorder : Expr) : Expr :=
  mkApp2 (.const ``LE.le [u]) α (mkApp2 (.const ``Preorder.toLE [u]) α preorder)

def mkLT (u : Level) (α preorder : Expr) : Expr :=
  mkApp2 (.const ``LT.lt [u]) α (mkApp2 (.const ``Preorder.toLT [u]) α preorder)

private inductive Pattern where
  | le
  | lt
  | imp
deriving BEq

def PropPreorder : Expr := mkApp2 (.const ``PartialOrder.toPreorder [.zero]) (.sort .zero) (.const ``Prop.partialOrder [])

def getLEsides (u : Level) (rel α preorder target : Expr) : MetaM (Pattern × Expr × Expr) :=
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
    if ← isDefEq preorder PropPreorder then
      return (.imp, lhs, rhs)

    throwError m! "expected an inequality for {target} : {α}, not {indentExpr rel}"

  | _ => throwError m! "expected an inequality for {target} : {α}, not {indentExpr rel}"


def getLEsides! : Pattern → Expr → Expr × Expr
  | .imp, .forallE _ lhs rhs _  => (lhs, rhs)
  | _   , .app (.app _ lhs) rhs => (lhs, rhs)
  | _, _ => panic! ""

def rewriteOrdUnify (fvars : Array Expr) (u : Level) (α preorder rel target : Expr) (hypContext : HypothesisContext) (pol : Bool) : MetaM' (Expr × Expr) := do
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




partial def visit [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadError m] [MonadMCtx m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
  (k : Array Expr → Level → Expr → Expr → Expr → Bool → m (Expr × Expr)) (u : Level) (α preorder : Expr) (fvars : Array Expr) (pol : Bool) : List Nat → Expr → m (Expr × Expr)
  -- write lhs for the original subexpressiont, and rhs for the replaced subexpression
  | xs, .mdata d lhs => do
    let (rhs, h) ← visit k u α preorder fvars pol xs lhs
    return (.mdata d rhs, h)

  | [], lhs => k fvars u α preorder lhs pol
    
  | 0::xs, .app lhs a => do
    let α' ← inferType a
    let v ← getDecLevel α'
    let uNew := (Level.imax v u).normalize
    let (rhs, h) ← visit k uNew (.forallE `_a α' α .default) (mkApp3 (.const ``Pi.ndPreorder [v, u]) α' α preorder) fvars pol xs lhs
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
    
    let (rhs, h) ← visit k uNew typeNew preorder' fvars (pol != anti) xs lhs
    return (.app f rhs, ← mkAppOptM' monoProof #[none, none, h])


  | 2::xs, .letE n t v lhs d => do 
    withLocalDeclD n (t.instantiateRev fvars) fun fvar => do
    let (rhs, h) ← visit k u α preorder (fvars.push fvar) pol xs (lhs.instantiate1 fvar)
    
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

    let (rhs, h) ← visit k v β (← instantiateMVars newPreorder) (fvars.push fvar) pol xs (lhs.instantiate1 fvar)
    return (.lam n t (rhs.abstract #[fvar]) bi, .lam n t (h.abstract #[fvar]) bi)


  | 0::xs, .forallE n lhs b bi => do
    unless ← isDefEq preorder PropPreorder do
      throwError m!"Prop is the only type with an order{indentExpr b}"
    let (rhs, h) ← visit k u α preorder fvars (!pol) xs lhs
    let h   := mkApp2 (mkConst ``id [.zero]) ((if pol then id else swap) (mkApp2 (mkLE u α preorder)) lhs rhs) h
    return (.forallE n rhs b bi, mkApp ((if pol then id else swap) (mkApp3 (.const ``imp_left_anti' []) b) lhs rhs) h)

  | 1::xs, .forallE n t lhs bi => do
    unless ← isDefEq preorder PropPreorder do
      throwError m!"Prop is the only type with an order{indentExpr lhs}"

    withLocalDecl n bi (t.instantiateRev fvars) fun fvar => do
    let (rhs, h) ← visit k u α preorder (fvars.push fvar) pol xs (lhs.instantiate1 fvar)
    let h   := mkApp2 (mkConst ``id [.zero]) ((if pol then swap else id) (mkApp2 (mkLE u α preorder)) lhs rhs) h
    let h   := .lam n t (h.abstract #[fvar]) bi
    
    let lhs := .lam n t (lhs.abstract #[fvar]) bi
    let rhs := rhs.abstract #[fvar]
    let (rhs, rhs') := (.forallE n t rhs bi, .lam n t rhs bi)
    
    return (rhs, mkApp ((if pol then swap else id) (mkApp3 (.const  ``forall_mono [← getLevel t]) t) lhs rhs') h)

  | list, lhs => throwError "could not find sub position {list} in '{lhs}'"

partial def treeRewriteOrd (hypContext : HypothesisContext) (rel target : Expr) (pol : Bool) (hypPath : List TreeBinderKind) (hypPos goalPos : List Nat) : MetaM' TreeProof := do
  unless hypPath == [] do
    throwError m! "cannot rewrite using a subexpression: subtree {hypPath} in {rel}"
  unless hypPos == [] do
    throwError m! "cannot rewrite using a subexpression: expression {hypPos} in {rel}"
  let (newTree, proof) ← visit (fun fvars u α preorder lhs pol => rewriteOrdUnify fvars u α preorder rel lhs hypContext pol) (.zero) (.sort .zero) PropPreorder #[] pol goalPos target
  return ({ newTree, proof })

def getPolarity (pos : List Nat) (tree : Expr) : MetaM Bool :=
  let (path, pos) := posToPath pos tree
  withTreeSubexpr tree [] (fun pol e => do
    let Except.error pol ← show ExceptT Bool MetaM _ from visit (fun _ _ _ _ _ pol => MonadExceptOf.throw pol) (.zero) (.sort .zero) PropPreorder #[] pol pos e | unreachable!
    return pol) (some path)

open Elab.Tactic

elab "tree_rewrite_ord" hypPos:treePos goalPos:treePos : tactic  => do
  let hypPos := getPosition hypPos
  let goalPos := getPosition goalPos
  workOnTree (applyBound hypPos goalPos true treeRewriteOrd)

elab "tree_rewrite_ord'" hypPos:treePos goalPos:treePos : tactic  => do
  let hypPos := getPosition hypPos
  let goalPos := getPosition goalPos
  workOnTree (applyBound hypPos goalPos false treeRewriteOrd)

def getRewriteOrdPos (hypPos : Option (List Nat)) (hyp : Expr) (_goalPath : List TreeBinderKind) : MetaM (Expr × List TreeBinderKind × List Nat) := do
  let hypTree ← makeTree hyp
  let (path, pos) := match hypPos with
    | some pos => posToPath pos hypTree
    | none => (findPath hypTree, [])
  return (← makeTreePath path hyp, path, pos)

elab "lib_rewrite_ord" hypPos:(treePos)? hypName:ident goalPos:treePos : tactic => do
  let hypName ← Elab.resolveGlobalConstNoOverloadWithInfo hypName
  let goalPos := getPosition goalPos
  let hypPos := getPosition <$> hypPos
  workOnTree (applyUnbound hypName (getRewriteOrdPos hypPos) goalPos treeRewriteOrd)

open DiscrTree in 
def librarySearchRewriteOrd (goalPos : List Nat) (tree : Expr) : MetaM (Array (Array (Name × AssocList SubExpr.Pos Widget.DiffTag × String) × Nat)) := do
  let discrTrees ← getLibraryLemmas
  let pol ← getPolarity goalPos tree

  let results := if pol
    then (← getSubExprUnify discrTrees.2.rewrite_ord     tree goalPos) ++ (← getSubExprUnify discrTrees.1.rewrite_ord     tree goalPos)
    else (← getSubExprUnify discrTrees.2.rewrite_ord_rev tree goalPos) ++ (← getSubExprUnify discrTrees.1.rewrite_ord_rev tree goalPos)
  let results ← filterLibraryResults results fun {name, path, pos, ..} => do
    try
      _ ← applyUnbound name (fun hyp _goalPath => return (← makeTreePath path hyp, path, pos)) goalPos treeRewriteOrd tree
      return true
    catch _ =>
      return false

  return results.map $ Bifunctor.fst $ Array.map fun {name, path, pos, diffs} => (name, diffs, s! "lib_rewrite_ord {pathPosToPos path pos} {name} {goalPos}")

elab "try_lib_rewrite_ord" goalPos:treePos : tactic => do
  let goalPos := getPosition goalPos
  let tree := (← getMainDecl).type
  logLibrarySearch (← librarySearchRewriteOrd goalPos tree)



-- example (a : ℝ) : dist a b < 5 := by
--   revert a
--   make_tree
--   try_lib_rewrite_ord [1,0,1]

-- example (n : Nat) : n ≤ n - 3  := by
--   try_lib_rewrite_ord [1]

example : (0 ≤ 1) → 0 ≤ 1 := by
  make_tree
  tree_rewrite_ord [0] [1,0,1]
  rfl

example (p q : Prop) : (p → q) → True ∨ (p → q) := by
  make_tree
  tree_rewrite_ord [0] [1,1,1]
  sorry

example (p q : Prop) : Imp (p → q) <| True ∨ (p → q) := by
  tree_rewrite_ord [0] [1,1,1]
  sorry

example (p q : Prop) : Imp (p → q) <| True ∨ (p → q) := by
  tree_rewrite_ord [0] [1,1,0]
  sorry

example (𝔸 : Set (Set α)) (B C : Set α) : (C ⊆ B) → {A ∈ 𝔸 | B ⊂ A} ⊆ {A ∈ 𝔸 | C ⊂ A} := by
  make_tree
  tree_rewrite_ord [0] [1,0,1,1,1,1,0,1]
  rfl

lemma testLib : ∀ x, x - 1 ≤ x := sorry

example : (∀ x, x - 1 ≤ x) → {x : Nat | x ≤ 4 } ⊆ {x : Nat | x - 1 ≤ 4} := by
  make_tree
  lib_rewrite_ord [1] Tree.testLib [1,0,1,1,1,0,1]
  lib_apply _root_.refl [1]

example : Imp (Forall ℕ fun x => x - 1 ≤ x) <| ∃ n, n - 1 ≤ n := by
  tree_rewrite_ord [0,1] [1,1,1,1]
  use 0    

example : Imp (Forall ℕ fun x => x - 1 ≤ x) <| ∀ n, n - 1 ≤ n := by
  tree_rewrite_ord [0,1] [1,1,1]
  make_tree
  lib_apply _root_.refl [1]

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

