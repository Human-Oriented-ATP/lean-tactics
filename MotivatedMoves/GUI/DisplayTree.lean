import MotivatedMoves.ProofState.Tree

namespace Tree
open Lean Parser

def newLineTermParser := ppDedent ("⠀" >> ppLine >> categoryParser `tree 0)

declare_syntax_cat symbol_binder
declare_syntax_cat binder
declare_syntax_cat tree

syntax ident "⋆ : " term : binder
syntax ident "• : " term : binder
syntax ident " : " term : binder
syntax "[" (ident " : ")? term "]" : binder

syntax ("∀ " <|> "∃ ")? binder : symbol_binder

syntax (name := binders) symbol_binder,+ newLineTermParser : tree
syntax (name := hypothesis) term newLineTermParser : tree
syntax (name := dotHypothesis) "·" ppHardSpace term newLineTermParser : tree
syntax (name := sidegoal) "⊢" ppHardSpace term newLineTermParser : tree

def newLine := ppDedent (ppLine >> categoryParser `term 0)
syntax (name := firstLine) newLine : tree

syntax ident "•" : term
syntax ident "⋆" : term


open PrettyPrinter.Delaborator SubExpr TSyntax.Compat

/--
For each node in the tree, specify hoe the syntax should be and which part of the syntax gets annotated with term info,
so that it can be clicked on. The SubExpr.Pos encoding is using 0 or 1 within the tree, and uses a 2 to denote the transition to 
a regular expression. -/
partial def delabTreeAux (pol : Bool) (root := false) : Delab := do
  match ← getExpr with
  | forall_pattern n _u d b =>
    let stxD ← withAppFn $ withAppArg delab
    let n ← getUnusedName n b
    let stxN := mkIdent n
    let stxND ← annotateTermInfo (← if pol then `(binder| $stxN:ident : $stxD) else `(binder| $stxN:ident⋆ : $stxD))
    Meta.withLocalDeclD n d fun fvar =>
    descend (b.instantiate1 (if pol then fvar else mkAnnotation `star fvar)) 1 do
    match ← (delabTreeAux pol) with
      | `(tree|∀ $a:binder⠀ $stx)                        => `(tree|∀ $stxND:binder, $a:binder⠀ $stx)
      | `(tree|∀ $a:binder, $[$b:symbol_binder],*⠀ $stx) => `(tree|∀ $stxND:binder, $a:binder, $[$b:symbol_binder],*⠀ $stx)
      | `(tree|$[$b:symbol_binder],*⠀ $stx)              => `(tree|∀ $stxND:binder, $[$b:symbol_binder],*⠀ $stx)
      | `(tree|$stx)                                     => `(tree|∀ $stxND:binder⠀ $stx)

  | exists_pattern n _u d b =>
    let stxD ← withAppFn $ withAppArg delab
    let n ← getUnusedName n b
    let stxN := mkIdent n
    let stxND ← annotateTermInfo (← if pol then `(binder| $stxN:ident• : $stxD) else `(binder| $stxN:ident : $stxD))
    Meta.withLocalDeclD n d fun fvar =>
    descend (b.instantiate1 (if pol then mkAnnotation `bullet fvar else fvar)) 1 do
    match ← (delabTreeAux pol) with
      | `(tree|∃ $a:binder⠀ $stx)                        => `(tree|∃ $stxND:binder, $a:binder⠀ $stx)
      | `(tree|∃ $a:binder, $[$b:symbol_binder],*⠀ $stx) => `(tree|∃ $stxND:binder, $a:binder, $[$b:symbol_binder],*⠀ $stx)
      | `(tree|$[$b:symbol_binder],*⠀ $stx)              => `(tree|∃ $stxND:binder, $[$b:symbol_binder],*⠀ $stx)
      | `(tree|$stx)                                     => `(tree|∃ $stxND:binder⠀ $stx)

  | instance_pattern n _u d b =>
    let stxD ← withAppFn $ withAppArg delab
    let stxND ← annotateTermInfo <| ← do 
      if n.eraseMacroScopes == `inst then `(binder| [$stxD:term])
      else do
      let n ← getUnusedName n b
      let stxN := mkIdent n
      `(binder| [$stxN:ident : $stxD])
    Meta.withLocalDeclD n d fun fvar =>
    descend (b.instantiate1 (mkAnnotation `bullet fvar)) 1 do
    match ← (delabTreeAux pol) with
      | `(tree|$[$b:symbol_binder],*⠀ $stx) => `(tree|$stxND:binder, $[$b:symbol_binder],*⠀ $stx)
      | `(tree|$stx)                        => `(tree|$stxND:binder⠀ $stx)

  | imp_pattern p q =>
    let stxP ← descend p 0 (delabTreeAux !pol)
    let stxQ ← descend q 1 (delabTreeAux  pol)
    annotateTermInfo =<< if isTree p
    then
      `(dotHypothesis|· $stxP⠀$stxQ)
    else
      `(hypothesis|$stxP⠀$stxQ)

  | and_pattern p q =>
    let stxP ← descend p 0 (delabTreeAux pol)
    let stxQ ← descend q 1 (delabTreeAux pol)
    annotateTermInfo =<< `(sidegoal|⊢ $stxP⠀$stxQ)
  
  | not_pattern p =>
    let stx ← descend p 0 (delabTreeAux !pol)
    annotateTermInfo =<< `(¬ $stx)

  | e => if root then failure else descend e 2 delab


@[delab app.Tree.Forall, delab app.Tree.Exists, delab app.Tree.Instance, delab app.Tree.Imp, delab app.Tree.And, delab app.Tree.Not]
def delabTree : Delab :=
  delabTreeAux true true

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

open Widget in
def ppTreeTagged (e : Expr) : MetaM CodeWithInfos := do
  if pp.raw.get (← getOptions) then
    return .text (toString e)
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos e (delab := delabTreeAux true)
  let tt := TaggedText.prettyTagged fmt
  let ctx := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }
  return tagCodeInfos ctx infos tt



example (p : Prop) (q : Nat → Prop) : ∀ x : Nat, ([LE ℕ] → [r: LE ℕ] →  ∀ a : Nat, ¬ ∃ g n : Int, ∃ m:Nat, Nat → q a) → p → ¬ (p → p) → ∃ m h : Nat, q m := by
  make_tree
  sorry
example (p : Prop) : ∀ x : Nat, ∀ y : Nat, ↑x = y := by
  make_tree
  sorry
