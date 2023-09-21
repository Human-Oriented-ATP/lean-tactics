import Tree

namespace Tree
open Lean Parser

def newLineTermParser := ppDedent ("⠀" >> ppLine >> categoryParser `tree 0)

declare_syntax_cat symbol_binder
declare_syntax_cat binder
declare_syntax_cat tree

syntax ident "⋆ : " term : binder
syntax ident "• : " term : binder
syntax "[" (ident " : ")? term "]" : binder

syntax ("∀ " <|> "∃ ")? binder : symbol_binder

syntax (name := binders) symbol_binder,+ newLineTermParser : tree
syntax (name := hypothesis) term newLineTermParser : tree
syntax (name := dotHypothesis) "·" ppHardSpace term newLineTermParser : tree
syntax (name := sidegoal) "⊢" ppHardSpace term newLineTermParser : tree

syntax ident "•" : term
syntax ident "⋆" : term


open PrettyPrinter.Delaborator SubExpr TSyntax.Compat

@[delab app.Tree.Forall]
def delabForall : Delab := do
  let forall_pattern n _u d b ← getExpr | failure
  let stxD ← withAppFn $ withAppArg delab
  let n ← getUnusedName n b
  let stxN := mkIdent n
  let stxND ← annotateTermInfo (← `(binder| $stxN:ident⋆ : $stxD))
  Meta.withLocalDeclD n d fun fvar =>
  descend (b.instantiate1 (mkAnnotation `star fvar)) 1 do
  match ← delab with
    | `(tree|∀ $a:binder, $[$b:symbol_binder],*⠀ $stx) => `(tree|∀ $stxND:binder, $a:binder, $[$b:symbol_binder],*⠀ $stx)
    | `(tree|$[$b:symbol_binder],*⠀ $stx)             => `(tree|∀ $stxND:binder, $[$b:symbol_binder],*⠀ $stx)
    | `(tree|$stx)                                    => `(tree|∀ $stxND:binder⠀ $stx)

@[delab app.Tree.Exists]
def delabExists : Delab := do
  let exists_pattern n _u d b ← getExpr | failure
  let stxD ← withAppFn $ withAppArg delab
  let n ← getUnusedName n b
  let stxN := mkIdent n
  let stxND ← annotateTermInfo (← `(binder| $stxN:ident• : $stxD))
  Meta.withLocalDeclD n d fun fvar =>
  descend (b.instantiate1 (mkAnnotation `bullet fvar)) 1 do
  match ← delab with
    | `(tree|∃ $a:binder, $[$b:symbol_binder],*⠀ $stx) => `(tree|∃ $stxND:binder, $a:binder, $[$b:symbol_binder],*⠀ $stx)
    | `(tree|$[$b:symbol_binder],*⠀ $stx)             => `(tree|∃ $stxND:binder, $[$b:symbol_binder],*⠀ $stx)
    | `(tree|$stx)                                    => `(tree|∃ $stxND:binder⠀ $stx)

@[delab app.Tree.Instance]
def delabInstance : Delab := do
  let instance_pattern n _u d b ← getExpr | failure
  let stxD ← withAppFn $ withAppArg delab
  let stxND ← annotateTermInfo <| ← do 
    if n.eraseMacroScopes == `inst then `(binder| [$stxD:term])
    else do
    let n ← getUnusedName n b
    let stxN := mkIdent n
    `(binder| [$stxN:ident : $stxD])
  Meta.withLocalDeclD n d fun fvar =>
  descend (b.instantiate1 (mkAnnotation `bullet fvar)) 1 do
  match ← delab with
    | `(tree|$[$b:symbol_binder],*⠀ $stx) => `(tree|$stxND:binder, $[$b:symbol_binder],*⠀ $stx)
    | `(tree|$stx)                        => `(tree|$stxND:binder⠀ $stx)

@[delab app.Tree.Imp]
def delabImp : Delab := do
  let imp_pattern p q ← getExpr | failure
  let stxP ← descend p 0 delab
  let stxQ ← descend q 1 delab
  if isTree p then
    `(dotHypothesis|· $stxP⠀$stxQ)
  else
    `(hypothesis|$stxP⠀$stxQ)

@[delab app.Tree.And]
def delabAnd : Delab := do
  let and_pattern p q ← getExpr | failure
  let stxP ← descend p 0 delab
  let stxQ ← descend q 1 delab
  `(sidegoal|⊢ $stxP⠀$stxQ)


/- note that we do not call the main delab function, but delabFVar directly. This is to avoid a seccond term annotation
on the free variable itself, without the bullet/star.-/
@[delab mdata]
def delabAnnotation : Delab := do
  if (annotation? `star (← getExpr)).isSome then
    `($(← withMDataExpr delabFVar):ident ⋆)
  else
  if (annotation? `bullet (← getExpr)).isSome then
    `($(← withMDataExpr delabFVar):ident •)
  else failure


example (p : Prop) (q : Nat → Prop) : ([LE ℕ] → [r: LE ℕ] →  ∀ a : Nat, ∃ g n : Int, ∃ m:Nat, Nat → q a) →  p → (p → p) → ∃ m h : Nat, q m := by
  make_tree
  sorry
example (p : Prop) : ∀ x : Nat, ∀ y : Nat, ↑x = y := by
  make_tree
  sorry

