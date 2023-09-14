import Tree

namespace Tree

open Lean TSyntax.Compat Parser

def newLineTermParser := ppDedent $ "⠀" >> ppLine >> termParser

syntax "∀ " ident "* : " term newLineTermParser : term
syntax "∃ " ident "• : " term newLineTermParser : term
syntax "[" ident " : " term "]" newLineTermParser : term
syntax "⬐" ppHardSpace term newLineTermParser : term
syntax "⊢" ppHardSpace term newLineTermParser : term

syntax ident "•" : term
syntax ident "*" : term

macro_rules
| `(∀ $a* : $b⠀$c) => `(Tree.Forall $b fun $a => $c)
| `(∃ $a• : $b⠀$c) => `(Tree.Exists $b fun $a => $c)
| `([$a : $b]⠀$c) => `(Tree.Instance $b fun $a => $c)
| `(⬐ $a⠀$b) => `(Tree.Imp $a $b)
| `(⊢ $a⠀$b) => `(Tree.And $a $b)
| `($a:ident *) => `($a)
| `($a:ident •) => `($a)

-- @[app_unexpander Forall] def unexpandForall' : Lean.PrettyPrinter.Unexpander
--   | `($(_) $t fun $x:ident => $b)
--   | `($(_) $t fun ($x:ident : $_) => $b) => `(∀ $x:ident* : $t⠀$b)
--   | _ => throw ()

-- @[app_unexpander Exists] def unexpandExists' : Lean.PrettyPrinter.Unexpander
--   | `($(_) $t fun $x:ident => $b)
--   | `($(_) $t fun ($x:ident : $_) => $b) => `(∃ $x:ident• : $t⠀$b)
--   | _ => throw ()

@[app_unexpander Imp] def unexpandImp : Lean.PrettyPrinter.Unexpander
  | `($(_) $P $Q) => `(⬐ $P⠀$Q)--`($P ⇨ $Q)
  | _ => throw ()

@[app_unexpander And] def unexpandAnd : Lean.PrettyPrinter.Unexpander
  | `($(_) $P $Q) => `(⊢ $P⠀$Q)--`($P ∧ $Q)
  | _ => throw ()

-- @[app_unexpander Imp'] def unexpandImp' : Lean.PrettyPrinter.Unexpander
--   | `($(_) $P fun $x:ident => $b)
--   | `($(_) $P fun ($x:ident : $_) => $b) => `(⬐ ($x : $P)⠀$b)--`(($x : $P) ⇨ $b)
--   | _ => throw ()

-- @[app_unexpander And'] def unexpandAnd' : Lean.PrettyPrinter.Unexpander
--   | `($(_) $P fun $x:ident => $b)
--   | `($(_) $P fun ($x:ident : $_) => $b) => `(⊢ ($x : $P)⠀$b)--`(($x : $P) ∧ $b)
--   | _ => throw ()
  
@[app_unexpander Instance] def unexpandInstance : Lean.PrettyPrinter.Unexpander
  | `($(_) $P fun $x:ident => $b)
  | `($(_) $P fun ($x:ident : $_) => $b) => `([$x : $P]⠀$b)
  | _ => throw ()


open PrettyPrinter.Delaborator SubExpr



@[delab app.Tree.Forall]
def delabForall : Delab := do
  let forall_pattern n _u d b ← getExpr | failure
  let n ← getUnusedName n b
  let stxD ← withAppFn $ withAppArg $ delab
  let stxB ← Meta.withLocalDeclD n d fun fvar => do
    let b := b.instantiate1 (mkAnnotation `star fvar)
    withAppArg $ descend b 1 delab
  let stxN := mkIdent n
  `(∀ $stxN* : $stxD⠀$stxB)
  
@[delab app.Tree.Exists]
def delabExists : Delab := do
  let exists_pattern n _u d b ← getExpr | failure
  let n ← getUnusedName n b
  let stxD ← withAppFn $ withAppArg $ delab
  let stxB ← Meta.withLocalDeclD n d fun fvar => do
    let b := b.instantiate1 (mkAnnotation `bullet fvar)
    withAppArg $ descend b 1 delab
  let stxN := mkIdent n
  `(∃ $stxN• : $stxD⠀$stxB)
  


@[delab mdata]
def delabAnnotation : Delab := do
  if (annotation? `star (← getExpr)).isSome then
    `($(← withMDataExpr delab):ident *)
  else
  if (annotation? `bullet (← getExpr)).isSome then
    `($(← withMDataExpr delab):ident •)
  else failure


example (p : Prop) (q : Nat → Prop) :( ∀ n : Nat, q n) →  p → (p → p) →  ∃ m : Nat, q m := by
  make_tree
  sorry
