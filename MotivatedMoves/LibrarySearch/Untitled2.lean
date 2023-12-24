import Lean

namespace MLList2

private structure Spec (m : Type u → Type u) where
  listM : Type u → Type u
  nil : listM α
  cons : α → listM α → listM α
  squash : (m (listM α)) → listM α
  uncons : [Monad m] → listM α → m (Option (α × listM α))

instance : Nonempty (Spec m) := .intro
  { listM := fun _ => PUnit
    nil := ⟨⟩
    cons := fun _ _ => ⟨⟩
    squash := fun _ => ⟨⟩
    uncons := fun _ => pure none }

private unsafe inductive MLListImpl (m : Type u → Type u) (α : Type u) : Type u
  | nil : MLListImpl m α
  | cons : α → MLListImpl m α → MLListImpl m α
  | squash : ( m (MLListImpl m α)) → MLListImpl m α

private unsafe def unconsImpl {m : Type u → Type u} [Monad m] :
    MLListImpl m α → m (Option (α × MLListImpl m α))
  | .nil => pure none
  | .squash t => t >>= unconsImpl
  | .cons x xs => return (x, xs)

@[inline] private unsafe def specImpl (m) : Spec m where
  listM := MLListImpl m
  nil := .nil
  cons := .cons
  squash := .squash
  uncons := unconsImpl

@[implemented_by specImpl]
private opaque spec (m) : MLList2.Spec m

end MLList2

def MLList2 (m : Type u → Type u) (α : Type u) : Type u := (MLList2.spec m).listM α

namespace MLList2

@[inline] def nil : MLList2 m α := (MLList2.spec m).nil

@[inline] def cons : α → MLList2 m α → MLList2 m α := (MLList2.spec m).cons

def squash : ( m (MLList2 m α)) → MLList2 m α := (MLList2.spec m).squash

@[inline] def uncons [Monad m] : MLList2.{u} m α → m (Option (α × MLList2 m α)) :=
  (MLList2.spec m).uncons

instance : Inhabited (MLList2 m α) := ⟨nil⟩
def x : Nat := 2
partial def mapNatTrans [Monad m] (f : ∀ {α}, m α → n α) : MLList2 n Unit :=
  squash $ f <| do
    match ← nil.uncons (α := Unit) with
    | none => return nil
    | some _ => return (mapNatTrans f)

open Lean.Meta
def g : MLList2 MetaM Unit := MLList2.mapNatTrans id
/-
(kernel) function expected
  _x_163 a✝²² a✝²¹ a✝²⁰ a✝¹⁹ a✝¹⁶
-/
