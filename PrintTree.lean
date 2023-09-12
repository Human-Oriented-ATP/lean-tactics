import Tree

namespace Tree

open Lean TSyntax.Compat Parser

def newLineTerm := ppDedent $ ";" >> ppLine >> termParser

syntax (name := forAllStx) "∀ " ident " : " ppHardSpace term newLineTerm : term
syntax "∃ " ident " : " term newLineTerm : term
syntax "[" ident " : " term "]" newLineTerm : term
-- syntax term " ⇨ " term : term
syntax "⬐ " term newLineTerm : term
syntax "⊢ " term newLineTerm : term

@[app_unexpander Forall] def unexpandForall' : Lean.PrettyPrinter.Unexpander
  | `($(_) $t fun $x:ident => $b)
  | `($(_) $t fun ($x:ident : $_) => $b) => `(∀ $x:ident : $t; $b)
  | _ => throw ()

@[app_unexpander Exists] def unexpandExists' : Lean.PrettyPrinter.Unexpander
  | `($(_) $t fun $x:ident => $b)
  | `($(_) $t fun ($x:ident : $_) => $b) => `(∃ $x:ident : $t; $b)
  | _ => throw ()

@[app_unexpander Imp] def unexpandImp : Lean.PrettyPrinter.Unexpander
  | `($(_) $P $Q) => `(⬐ $P; $Q)--`($P ⇨ $Q)
  | _ => throw ()

@[app_unexpander And] def unexpandAnd : Lean.PrettyPrinter.Unexpander
  | `($(_) $P $Q) => `(⊢ $P; $Q)--`($P ∧ $Q)
  | _ => throw ()

@[app_unexpander Imp'] def unexpandImp' : Lean.PrettyPrinter.Unexpander
  | `($(_) $P fun $x:ident => $b)
  | `($(_) $P fun ($x:ident : $_) => $b) => `(⬐ ($x : $P); $b)--`(($x : $P) ⇨ $b)
  | _ => throw ()

@[app_unexpander And'] def unexpandAnd' : Lean.PrettyPrinter.Unexpander
  | `($(_) $P fun $x:ident => $b)
  | `($(_) $P fun ($x:ident : $_) => $b) => `(⊢ ($x : $P); $b)--`(($x : $P) ∧ $b)
  | _ => throw ()
  
@[app_unexpander Instance] def unexpandInstance : Lean.PrettyPrinter.Unexpander
  | `($(_) $P fun $x:ident => $b)
  | `($(_) $P fun ($x:ident : $_) => $b) => `([$x : $P]; $b)
  | _ => throw ()

-- example (p : Prop) (q : Nat → Prop) :( ∀ n : Nat, q n) →  p → (p → p) →  ∃ m : Nat, q m := by
--   make_tree
--   sorry
