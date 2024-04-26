import MotivatedMoves.ProofState.Tree
import ProofWidgets.Compat

namespace Tree

open Lean Meta ProofWidgets


def editTree (edit : Expr → MetaM Expr) : OuterPosition → Expr → MetaM Expr
  | 1::xs, forall_pattern   n u d tree => withLocalDeclD n d fun fvar => return mkForall   n u d ((← editTree edit xs (tree.instantiate1 fvar)).abstract #[fvar])
  | 1::xs, exists_pattern   n u d tree => withLocalDeclD n d fun fvar => return mkExists   n u d ((← editTree edit xs (tree.instantiate1 fvar)).abstract #[fvar])
  | 1::xs, instance_pattern n u d tree => withLocalDeclD n d fun fvar => return mkInstance n u d ((← editTree edit xs (tree.instantiate1 fvar)).abstract #[fvar])
  | 1::xs, imp_pattern p tree => return mkImp p (← editTree edit xs tree)
  | 0::xs, imp_pattern tree p => return mkImp (← editTree edit xs tree) p
  | 1::xs, and_pattern p tree => return mkAnd p (← editTree edit xs tree)
  | 0::xs, and_pattern tree p => return mkAnd (← editTree edit xs tree) p
  | 1::xs, not_pattern tree   => return mkNot (← editTree edit xs tree)
  | [], e => edit e
  | xs, e => throwError m! "could not find position {xs} in {indentExpr e}"

partial def editExpr (edit : Expr → MetaM Expr) : InnerPosition → Expr → MetaM Expr
  | xs   , .mdata d b        => return .mdata d (← editExpr edit xs b)

  | 0::xs, .app f a          => return .app (← editExpr edit xs f) a
  | 1::xs, .app f a          => return .app f (← editExpr edit xs a)

  | 0::xs, .proj n i b       => return .proj n i (← editExpr edit xs b)

  | 0::xs, .letE n t v b d   => return .letE n (← editExpr edit xs t) v b d
  | 1::xs, .letE n t v b d   => return .letE n t (← editExpr edit xs v) b d
  | 2::xs, .letE n t v b d   => withLocalDeclD n t fun fvar =>
    return .letE n t v ((← editExpr edit xs (b.instantiate1 fvar)).abstract #[fvar]) d

  | 0::xs, .lam n t b bi     => return .lam n (← editExpr edit xs t) b bi
  | 1::xs, .lam n t b bi     => withLocalDeclD n t fun fvar =>
    return .lam n t ((← editExpr edit xs (b.instantiate1 fvar)).abstract #[fvar]) bi

  | 0::xs, .forallE n t b bi => return .forallE n (← editExpr edit xs t) b bi
  | 1::xs, .forallE n t b bi => withLocalDeclD n t fun fvar =>
    return .forallE n t ((← editExpr edit xs (b.instantiate1 fvar)).abstract #[fvar]) bi

  | []   , e                 => edit e
  | list , e                 => throwError m!"could not find subexpression {list} in '{e}'"

def edit (treePos : OuterPosition) (pos : InnerPosition) (edit : Expr → MetaM Expr) (tree : Expr) : MetaM Expr := do
  editTree (editExpr edit pos) treePos tree

open MonadExceptOf

partial def reduceProjection (e : Expr) : ExceptT MessageData MetaM Expr :=
  e.withAppRev fun f revArgs => match f with
    | .proj _ i b => do
      let some value ← project? b i | throw m! "could not project expression {b}"
      reduceProjection (value.betaRev revArgs)
    | _ => return e

def replaceByDefAux (e : Expr) : ExceptT MessageData MetaM Expr := do
  if let .letE _ _ v b _ := e then return b.instantiate1 v
  e.withAppRev fun f revArgs => match f with
    | .const name us => do
      let info ← getConstInfoDefn name
      let result := info.value.instantiateLevelParams info.levelParams us
      if ← isDefEq result f then
        reduceProjection (result.betaRev revArgs)
      else
        throw m! "could not replace {f} by its definition"
    | _ => do
      let result ← reduceProjection (f.betaRev revArgs)
      if result == e then throw m! "could not find a definition for {e}"
      else return result

def rewriteDef (goalOuterPosition : OuterPosition) (goalPos : InnerPosition) (tree : Expr) : MetaM (Option (ExprWithCtx × AssocList SubExpr.Pos Widget.DiffTag × String)) :=
  withTreeSubexpr tree goalOuterPosition goalPos fun _pol e => do
    match ← replaceByDefAux e with
    | .error _ => return none
    | .ok result => do
      let result ← ExprWithCtx.save result
      return some (result, AssocList.nil.cons SubExpr.Pos.root .wasChanged, s! "tree_rewrite_def {goalPos}")

def replaceByDef (e : Expr) : MetaM Expr := do
  match ← replaceByDefAux e with
  | .error e => throwError e
  | .ok result => return result


open Elab.Tactic in
elab "tree_rewrite_def" pos:treePos : tactic => do
  let (treePos, pos) := getOuterInnerPosition pos
  workOnTreeDefEq (edit treePos pos replaceByDef)
  let mkTree ← `(tactic | make_tree)
  evalTactic mkTree
