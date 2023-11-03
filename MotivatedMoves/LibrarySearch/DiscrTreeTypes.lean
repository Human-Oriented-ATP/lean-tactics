import Lean.Expr

/-! See file `DiscrTree.lean` for the actual implementation and documentation. -/

open Lean

namespace Tree.DiscrTree

/--
Discrimination tree key. See `DiscrTree`

The index of the star constructor gives a unique index for each star, giving each next star the next unused number.
-/
inductive Key where
  | const  : Name → Nat → Key
  | fvar   : Nat → Nat → Key
  | bvar   : Nat → Nat → Key
  | star   : Nat → Key
  | lit    : Literal → Key
  | other  : Key
  | lam    : Key
  | forall : Key
  | proj   : Name → Nat → Nat → Key
  deriving Inhabited, BEq, Repr

protected def Key.hash : Key → UInt64
  | .const n a   => mixHash 5237 $ mixHash (hash n) (hash a)
  | .fvar n a    => mixHash 3541 $ mixHash (hash n) (hash a)
  | .bvar i a    => mixHash 4323 $ mixHash (hash i) (hash a)
  | .star i      => mixHash 7883 $ hash i
  | .lit v       => mixHash 1879 $ hash v
  | .other       => 2411
  | .lam         => 4742
  | .«forall»    => 9752
  | .proj s i a  => mixHash (hash a) $ mixHash (hash s) (hash i)

instance : Hashable Key := ⟨Key.hash⟩

/--
Discrimination tree trie. See `DiscrTree`.
-/
inductive Trie (α : Type) where
  | node (vs : Array α) (children : Array (Key × Trie α))

end DiscrTree

open DiscrTree

/-!
Notes regarding term reduction at the `DiscrTree` module.
- In `simp`, we want to have `simp` theorem such as
```
@[simp] theorem liftOn_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Quot.liftOn (Quot.mk r a) f h = f a := rfl
```
If we enable `iota`, then the lhs is reduced to `f a`.
Note that when retrieving terms, we may also disable `beta` and `zeta` reduction.
See issue https://github.com/leanprover/lean4/issues/2669
- During type class resolution, we often want to reduce types using even `iota` and projection reductionn.
Example:
```
inductive Ty where
	@@ -80,7 +75,11 @@ def f (a b : Ty.bool.interp) : Ty.bool.interp :=
  test (.==.) a b
```
-/

/--
Discrimination trees. It is an index from terms to values of type `α`.
-/
structure DiscrTree (α : Type) where
  root : PersistentHashMap Key (Trie α) := {}

