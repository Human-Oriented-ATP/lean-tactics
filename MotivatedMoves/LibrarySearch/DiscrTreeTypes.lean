import Lean.Expr

/-! See file `DiscrTree.lean` for the actual implementation and documentation. -/

open Lean

namespace Tree.DiscrTree

/--
Discrimination tree key. See `DiscrTree`
-/
inductive Key where
  /-- `Key.const` takes a `Name` and the arity. -/
  | const  : Name → Nat → Key
  /-- `Key.fvar` takes an index and the arity. -/
  | fvar   : Nat → Nat → Key
  /-- `Key.bvar` takes an index and the arity. -/
  | bvar   : Nat → Nat → Key
  /-- `Key.star` takes an index. -/
  | star   : Nat → Key
  | lit    : Literal → Key
  | sort   : Key
  | lam    : Key
  | forall : Key
  /-- `Key.proj` takes the constructor `Name`, the projection index and the arity. -/
  | proj   : Name → Nat → Nat → Key
  deriving Inhabited, BEq, Repr

protected def Key.hash : Key → UInt64
  | .const n a   => mixHash 5237 $ mixHash (hash n) (hash a)
  | .fvar n a    => mixHash 3541 $ mixHash (hash n) (hash a)
  | .bvar i a    => mixHash 4323 $ mixHash (hash i) (hash a)
  | .star i      => mixHash 7883 $ hash i
  | .lit v       => mixHash 1879 $ hash v
  | .sort        => 2411
  | .lam         => 4742
  | .«forall»    => 9752
  | .proj s i a  => mixHash (hash a) $ mixHash (hash s) (hash i)

instance : Hashable Key := ⟨Key.hash⟩

/--
Discrimination tree trie. See `DiscrTree`.
-/
inductive Trie (α : Type) where
  | node (children : Array (Key × Trie α))
  | path (keys : Array Key) (child : Trie α)
  | values (vs : Array α)
end DiscrTree

open DiscrTree

/--
Discrimination trees. It is an index from terms to values of type `α`.
-/
structure DiscrTree (α : Type) where
  root : PersistentHashMap Key (Trie α) := {}

