import Lean

open Lean Elab Meta PrettyPrinter Delaborator SubExpr Parser

/-!
This file defines utilities to delaborate Lean expressions in a way suitable for export to SMT solvers.
-/

/-- This elaborator allows function applications to be written in uncurried style
    (e.g., `Nat.add(1, 2)` instead of the usual `Nat.add 1 2`). -/
elab (name := uncurried) f:ident noWs "(" args:term,* ")" : term => do
  let args ← args.getElems.mapM (Term.elabTerm · none)
  mkAppM f.getId args

#eval Nat.add((1 : Nat), (2 : Nat))

def Syntax.mkUncurriedApp (fnStx : Term) (argsStx : Array Term) : Term :=
  ⟨.node .none `uncurried #[
      fnStx.raw,
      .node .none `group #[],
      .atom .none "(",
      .node .none `null (mkSepArray argsStx (.atom .none ",")),
      .atom .none ")"
    ]⟩

/-- This is a modification of the implicit application delaborator defined in `Lean/PrettyPrinter/Delaborator/Builtins.lean`. -/
@[delab app]
def delabAppImplicit : Delab := do
  -- TODO: always call the unexpanders, make them guard on the right # args?
  let paramKinds ← getParamKinds
  if ← getPPOption getPPExplicit then
    if paramKinds.any (fun param => !param.isRegularExplicit) then failure

  -- If the application has an implicit function type, fall back to delabAppExplicit.
  -- This is e.g. necessary for `@Eq`.
  let isImplicitApp ← try
      let ty ← whnf (← inferType (← getExpr))
      pure <| ty.isForall && (ty.binderInfo == BinderInfo.implicit || ty.binderInfo == BinderInfo.instImplicit)
    catch _ => pure false
  if isImplicitApp then failure

  let tagAppFn ← getPPOption getPPTagAppFns
  let (fnStx, _, argStxs) ← withAppFnArgs
    (withOptionAtCurrPos `pp.tagAppFns tagAppFn <|
      return (← delabAppFn, paramKinds.toList, #[]))
    (fun (fnStx, paramKinds, argStxs) => do
      let arg ← getExpr
      let opts ← getOptions
      let mkNamedArg (name : Name) (argStx : TSyntax `term) : DelabM Syntax := do
        `(Parser.Term.namedArgument| ($(mkIdent name) := $argStx))
      let argStx? : Option Syntax ←
        if ← getPPOption getPPAnalysisSkip then pure none
        else if ← getPPOption getPPAnalysisHole then `(_)
        else
          match paramKinds with
          | [] => delab
          | param :: rest =>
            if param.defVal.isSome && rest.isEmpty then
              let v := param.defVal.get!
              if !v.hasLooseBVars && v == arg then pure none else delab
            else if !param.isRegularExplicit && param.defVal.isNone then
              if ← getPPOption getPPAnalysisNamedArg <||> (pure (param.name == `motive) <&&> shouldShowMotive arg opts) then some <$> mkNamedArg param.name (← delab) else pure none
            else delab
      let argStxs := match argStx? with
        | none => argStxs
        | some stx => argStxs.push ⟨stx⟩
      pure (fnStx, paramKinds.tailD [], argStxs))
  let stx := Syntax.mkUncurriedApp fnStx argStxs -- the syntax here is uncurried application instead of the usual curried syntax

  if ← isRegularApp then
    (guard (← getPPOption getPPNotation) *> unexpandRegularApp stx)
    <|> (guard (← getPPOption getPPStructureInstances) *> unexpandStructureInstance stx)
    <|> pure stx
  else pure stx

open Parser.Term

macro (name := fol_forall) "Forall" noWs "(" "[" binders:bracketedBinder,* "]" "," ppSpace body:term ")" : term =>
  -- let binders := binders.getElems
  `(∀ $binders:bracketedBinder*, $body)

/--
Similar to `delabBinders`, but tracking whether `forallE` is dependent or not.

See issue #1571
-/
private partial def delabForallBinders (delabGroup : TSyntaxArray `ident → Bool → Term → Delab) (curNames : TSyntaxArray `ident := #[]) (curDep := false) : Delab := do
  let dep := !(← getExpr).isArrow
  if !curNames.isEmpty && dep != curDep then
    -- don't group
    delabGroup curNames curDep (← delab)
  else
    let curDep := dep
    -- don't group => delab body and prepend current binder group
    let (stx, stxN) ← withBindingBodyUnusedName fun stxN => return (← delab, stxN)
    delabGroup (curNames.push (TSyntax.mk stxN)) curDep stx

open Parser.Term in
@[delab forallE]
def delabForall : Delab := do
  delabForallBinders fun curNames dependent stxBody => do
    let e ← getExpr
    let prop ← try isProp e catch _ => pure false
    let stxT ← withBindingDomain delab
    let group ← match e.binderInfo with
    | .implicit       => `(bracketedBinderF|{$curNames* : $stxT})
    | .strictImplicit => `(bracketedBinderF|⦃$curNames* : $stxT⦄)
    -- here `curNames.size == 1`
    | .instImplicit   => `(bracketedBinderF|[$curNames.back : $stxT])
    | .default                         =>
        -- if prop && !(← getPPOption getPPPiBinderTypes) then
        --   return ← `(∀ $curNames:ident*, $stxBody)
        -- else
        `(bracketedBinderF|($curNames* : $stxT))
    match stxBody with
    | `(Forall([$groups,*], $stxBody)) => `(Forall([$group, $groups,*], $stxBody))
    | _                       => `(Forall([$group], $stxBody))

example {P Q : Prop} : P → Q := by
  sorry

@[app_unexpander List.cons]
def listConsUnexpander : PrettyPrinter.Unexpander
  | `($(_) $h []) =>  `((singleton($h) : List _))
  | _ => throw ()

macro (name := fol_exists) "Exists" noWs "(" "[" binders:bracketedExplicitBinder,* "]" "," ppSpace body:term ")" : term =>
  `(∃ $binders:bracketedExplicitBinder*, $body)

@[app_unexpander Exists] def unexpandExists' : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => Exists([$xs:binderIdent,*], $b)) => `(Exists([$x:ident, $xs:binderIdent,*], $b))
  | `($(_) fun $x:ident => $b)                     => `(Exists([$x:ident], $b))
  | `($(_) fun ($x:ident : $t) => $b)              => `(Exists([($x:ident : $t)], $b))
  | _                                              => throw ()

set_option pp.notation false
set_option pp.funBinderTypes true
set_option pp.notation false
set_option pp.tagAppFns true
set_option pp.coercions false
set_option pp.analyze.typeAscriptions true
set_option pp.proofs.withType false
