import MotivatedMoves.ProofState.Tree
import ProofWidgets

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
    descend (b.instantiate1 fvar) 1 do
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
    let stx ← descend p 1 (delabTreeAux !pol)
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
def ppExprTaggedWith (e : Expr) (delab : Delab) : MetaM CodeWithInfos := do
  if pp.raw.get (← getOptions) then
    return .text (toString e)
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos e (delab := delab)
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

def ppTreeTagged := ppExprTaggedWith (delab := delabTreeAux true)

private def getUnusedName (suggestion : Name) (body : Expr) : MetaM Name := do
  -- Use a nicer binder name than `[anonymous]`. We probably shouldn't do this in all LocalContext use cases, so do it here.
  let suggestion := if suggestion.isAnonymous then `a else suggestion
  -- We use this small hack to convert identifiers created using `mkAuxFunDiscr` to simple names
  let suggestion := suggestion.eraseMacroScopes
  let lctx ← getLCtx
  if !lctx.usesUserName suggestion then
    return suggestion
  else if !bodyUsesSuggestion lctx suggestion then
    return suggestion
  else
    return lctx.getUnusedName suggestion
where
  bodyUsesSuggestion (lctx : LocalContext) (suggestion' : Name) : Bool :=
    Option.isSome <| body.find? fun
      | Expr.fvar fvarId =>
        match lctx.find? fvarId with
        | none      => false
        | some decl => decl.userName == suggestion'
      | _ => false

open Widget ProofWidgets Server

inductive DisplayTree where
| forall (quantifier : CodeWithInfos) (name : CodeWithInfos) (type : CodeWithInfos) (body : DisplayTree)
| exists (quantifier : CodeWithInfos) (name : CodeWithInfos) (type : CodeWithInfos) (body : DisplayTree)
| «instance» (inst : CodeWithInfos) (body : DisplayTree)
| implication (antecedent : DisplayTree) (arrow : CodeWithInfos) (consequent : DisplayTree)
| and (first : DisplayTree) (wedge : CodeWithInfos) (second : DisplayTree)
| not (not : CodeWithInfos) (body : DisplayTree)
| node (body : CodeWithInfos)
deriving RpcEncodable

/-- The number of pixels occupied by each row in the tree display. -/
def rowSize := 30
/-- The approximate width, in pixels, of a Unicode character in the chosen font. -/
def charWidth := 8
/-- The amount of horizontal padding to add around text in text bubbles. -/
def padding := 4

def DisplayTree.depth : DisplayTree → Nat
  | «forall» _ _ _ body => body.depth.succ
  | «exists» _ _ _ body => body.depth.succ
  | «instance» _ body => body.depth.succ
  | implication antecedent _ consequent => (antecedent.depth + consequent.depth).succ -- layering vertically
  | and first _ second => (max first.depth second.depth) -- displaying side-by-side
  | not _ body => body.depth
  | node _ => 1

def DisplayTree.width : DisplayTree → Nat
  | «forall» _ _ _ body => body.width
  | «exists» _ _ _ body => body.width
  | «instance» _ body => body.width
  | implication antecedent _ consequent => max antecedent.width consequent.width
  | and first _ second => rowSize + 2 * max first.width second.width
  | not _ body => rowSize + body.width
  | node e => e.stripTags.length * charWidth + padding * 2 * 2

open Lean PrettyPrinter
def annotateAs (txt : String) (e : SubExpr) (pos : SubExpr.Pos := .root) (delab : Delab := delab) : MetaM CodeWithInfos := do
  let (_stx, infos) ← delabCore e.expr {} delab
  let .some info := infos.find? pos | throwError m!"Could not find info for the expression {e.expr}."
  let ctx := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }
  let subexprInfo : SubexprInfo := {
    info := .mk {
      ctx := ctx,
      info := info,
      children := .empty
    },
    subexprPos := e.pos
  }
  return .tag subexprInfo (.text txt)

def annotateAsCurrentTree (txt : String) : DelabM CodeWithInfos := do
  annotateAs txt (← readThe SubExpr) .root (delabTreeAux true)

partial def toDisplayTree (pol := true) (root := false) : DelabM DisplayTree := do
  match (← getExpr) with
  | forall_pattern n _u d b =>
    let n ← getUnusedName n b
    let quantifierInfo ← annotateAsCurrentTree "∀"
    let domainInfo ← ppTreeTagged d 
    Meta.withLocalDeclD n d fun fvar => do
      let fvarAnnotated := if pol then fvar else mkAnnotation `star fvar
      let varInfo ← ppTreeTagged fvarAnnotated
      descend (b.instantiate1 fvarAnnotated) 1 do
        return .forall quantifierInfo varInfo domainInfo (← toDisplayTree pol)
  
  | exists_pattern n _u d b =>
    let n ← getUnusedName n b
    let quantifierInfo ← annotateAsCurrentTree "∃"
    let domainInfo ← ppTreeTagged d 
    Meta.withLocalDeclD n d fun fvar => do
      let fvarAnnotated := if pol then fvar else mkAnnotation `bullet fvar
      let varInfo ← ppTreeTagged fvarAnnotated
      descend (b.instantiate1 fvarAnnotated) 1 do
        return .exists quantifierInfo varInfo domainInfo (← toDisplayTree pol)
  
  | instance_pattern n _u d b =>
    Meta.withLocalDeclD n d fun fvar => do
      let n ← (do
        if n.eraseMacroScopes == `inst then
          return ""
        else
          return s! "{← getUnusedName n b} : ")
      descend (b.instantiate1 fvar) 1 do
        return .instance (.append #[.text s! "[{n}", ← ppTreeTagged d, .text "]"]) (← toDisplayTree pol)
  
  | imp_pattern p q =>
    let arrowInfo ← annotateAsCurrentTree "↓"
    let antecedent ← descend p 0 (toDisplayTree !pol)
    let consequent ← descend q 1 (toDisplayTree pol)
    return .implication antecedent arrowInfo consequent

  | and_pattern p q =>
    let andInfo ← annotateAsCurrentTree "∧"
    let fstGoal ← descend p 0 (toDisplayTree pol)
    let sndGoal ← descend q 1 (toDisplayTree pol)
    return .and fstGoal andInfo sndGoal

  | not_pattern p =>
    let notInfo ← annotateAsCurrentTree "¬"
    let body ← descend p 1 (toDisplayTree !pol)
    return .not notInfo body

  | e => 
    if root then 
      failure 
    else descend e 2 do
      return .node (← ppTreeTagged e)