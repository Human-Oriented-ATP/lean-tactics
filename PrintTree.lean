import Tree

namespace Tree

open Lean TSyntax.Compat

syntax "∀" explicitBinders "; " term : term
syntax "∃" explicitBinders "; " term : term
syntax term " ⇨ " term : term
-- syntax term " ∧ " term : term


@[app_unexpander Forall] def unexpandForall' : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b)                     => `(∀ $x:ident; $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∀ ($x:ident : $t); $b)
  | _                                              => throw ()

@[app_unexpander Exists] def unexpandExists' : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b)                     => `(∃ $x:ident; $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∃ ($x:ident : $t); $b)
  | _                                              => throw ()

@[app_unexpander Imp] def unexpandImp : Lean.PrettyPrinter.Unexpander
  | `($(_) $P $Q) => `($P ⇨ $Q)
  | _ => throw ()

@[app_unexpander And] def unexpandAnd : Lean.PrettyPrinter.Unexpander
  | `($(_) $P $Q) => `($P ∧ $Q)
  | _ => throw ()

@[app_unexpander Imp'] def unexpandImp' : Lean.PrettyPrinter.Unexpander
  | `($(_) $P fun $x:ident => $b) => `(($x : $P) ⇨ $b)
  | `($(_) $P fun $x:ident : $(_) => $b) => `(($x : $P) ⇨ $b)
  | _ => throw ()

@[app_unexpander And'] def unexpandAnd' : Lean.PrettyPrinter.Unexpander
  | `($(_) $P fun $x:ident => $b) => `(($x : $P) ∧ $b)
  | `($(_) $P fun $x:ident : $(_) => $b) => `(($x : $P) ∧ $b)
  | _ => throw ()