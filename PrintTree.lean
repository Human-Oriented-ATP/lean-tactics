import Tree

namespace Tree

open Lean TSyntax.Compat Parser

def newLineTermParser := ppDedent $ "⠀" >> ppLine >> termParser

syntax "∀ " ident "* : " term newLineTermParser : term
syntax "∃ " ident "• : " term newLineTermParser : term
syntax "[" ident " : " term "]" newLineTermParser : term
syntax "⬐ " term newLineTermParser : term
syntax "⊢ " term newLineTermParser : term

syntax ident "•" : term
syntax ident "*" : term

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

def mkAnnotatedIdent [Monad m] [MonadQuotation m] : Name → m Ident
| .str n "*" => `($(mkIdent n):ident *)
| .str n "•" => `($(mkIdent n):ident •)
| n => return mkIdent n

@[delab app.Tree.Forall]
def delabForall : Delab := do
  let e ← getExpr
  let forall_pattern n _u d b := e | failure
  let stxD ← withAppFn $ withAppArg $ delab
  let stxB ← Meta.withLocalDeclD (.str n "*") d fun fvar => do
    let b := b.instantiate1 fvar
    withAppArg $ descend b 1 delab
  let stxN := mkIdent n
  `(∀ $stxN* : $stxD⠀$stxB)
  
@[delab app.Tree.Exists]
def delabExists : Delab := do
  let e ← getExpr
  let exists_pattern n _u d b := e | failure
  let stxD ← withAppFn $ withAppArg $ delab
  let stxB ← Meta.withLocalDeclD (.str n "•") d fun fvar => do
    let b := b.instantiate1 fvar
    withAppArg $ descend b 1 delab
  let stxN := mkIdent n
  `(∃ $stxN• : $stxD⠀$stxB)
  

@[delab fvar]
def delabFVar : Delab := do
  let Expr.fvar fvarId ← getExpr | unreachable!
  let l ← try fvarId.getDecl catch _ => failure
  let id ← mkAnnotatedIdent l.userName
  maybeAddBlockImplicit id


-- example (p : Prop) (q : Nat → Prop) :( ∀ n : Nat, q n) →  p → (p → p) →  ∃ m : Nat, q m := by
--   make_tree
--   sorry
