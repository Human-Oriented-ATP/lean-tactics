import TreeMoves.Tree
import ProofWidgets.Compat

namespace Tree

open Lean Meta ProofWidgets


def editTree (edit : Expr → MetaM Expr) : List TreeBinderKind → Expr → MetaM Expr
  | .all ::xs, forall_pattern   n u d tree => withLocalDeclD n d fun fvar => return mkForall   n u d ((← editTree edit xs (tree.instantiate1 fvar)).abstract #[fvar])
  | .ex  ::xs, exists_pattern   n u d tree => withLocalDeclD n d fun fvar => return mkExists   n u d ((← editTree edit xs (tree.instantiate1 fvar)).abstract #[fvar])
  | .inst::xs, instance_pattern n u d tree => withLocalDeclD n d fun fvar => return mkInstance n u d ((← editTree edit xs (tree.instantiate1 fvar)).abstract #[fvar])
  | .imp_right::xs, imp_pattern p tree => return mkImp p (← editTree edit xs tree)
  | .imp_left ::xs, imp_pattern tree p => return mkImp (← editTree edit xs tree) p
  | .and_right::xs, and_pattern p tree => return mkAnd p (← editTree edit xs tree)
  | .and_left ::xs, and_pattern tree p => return mkAnd (← editTree edit xs tree) p
  | [], e => edit e
  | xs, e => throwError m! "could not find position {xs} in {indentExpr e}"

partial def editExpr (edit : Expr → MetaM Expr) : List Nat → Expr → MetaM Expr
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

def edit (pos : List Nat) (edit : Expr → MetaM Expr) (tree : Expr) : MetaM Expr := do
  let (path, pos) := posToPath pos tree
  editTree (editExpr edit pos) path tree

open MonadExceptOf

partial def reduceProjection (e : Expr) : ExceptT MessageData MetaM Expr :=
  e.withAppRev fun f revArgs => match f with
    | .proj _ i b => do
      let some value ← project? b i | throw m! "could not project expression {b}"
      reduceProjection (value.betaRev revArgs)
    | .lam .. => reduceProjection (f.betaRev revArgs)
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
      let result ← reduceProjection e
      if result == e then throw m! "could not find a definition for {e}"
      else return result

def rewriteDef (goalPos : List Nat) (tree : Expr) : MetaM (Option (ExprWithCtx × AssocList SubExpr.Pos Widget.DiffTag × String)) :=
  withTreeSubexpr tree goalPos fun _pol e => do
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
  let pos := getPosition pos
  workOnTreeDefEq (edit pos replaceByDef)

example : ∀ n:Nat, n + n = 2*n := by
  make_tree
  -- tree_rewrite_def [1,1]
  tree_rewrite_def [1,0,1]
  tree_rewrite_def [1,0,1]
  sorry

example : ∀ n:Nat, Prod.fst (n,n) = n := by
  make_tree
  tree_rewrite_def [1,0,1]
  sorry

example : (fun x => x) 1 = 1 := by
  tree_rewrite_def [0,1]
  rfl



def AbstractAux (depth : Nat) : List Nat → Expr → MetaM (Expr × Expr)
  | xs   , .mdata d b        => return Bifunctor.fst (.mdata d ·) (← AbstractAux depth xs b)
  
  | 0::xs, .app f a          => return Bifunctor.fst (.app · a) (← AbstractAux depth xs f)
  | 1::xs, .app f a          => return Bifunctor.fst (.app f ·) (← AbstractAux depth xs a)

  | 0::xs, .proj n i b       => return Bifunctor.fst (.proj n i ·) (← AbstractAux depth xs b)

  | 0::xs, .letE n t v b d   => return Bifunctor.fst (.letE n · v b d) (← AbstractAux depth xs t)
  | 1::xs, .letE n t v b d   => return Bifunctor.fst (.letE n t · b d) (← AbstractAux depth xs v)
  | 2::xs, .letE n t v b d   => return Bifunctor.fst (.letE n t v · d) (← AbstractAux (depth+1) xs b)
                                                    
  | 0::xs, .lam n t b bi     => return Bifunctor.fst (.lam n · b bi) (← AbstractAux depth xs t)
  | 1::xs, .lam n t b bi     => return Bifunctor.fst (.lam n t · bi) (← AbstractAux (depth+1) xs b)

  | 0::xs, .forallE n t b bi => return Bifunctor.fst (.forallE n · b bi) (← AbstractAux depth xs t)
  | 1::xs, .forallE n t b bi => return Bifunctor.fst (.forallE n t · bi) (← AbstractAux (depth+1) xs b)

  | []   , e                 => return (.bvar depth, e)
  | list , e                 => throwError m!"could not find subexpression {list} in '{e}'"

def betaAbstractAux (pos : List Nat) (e : Expr) : MetaM Expr := do
  let (b, v) ← AbstractAux 0 pos e
  if v.hasLooseBVars then throwError m! "cannot β-abstract a subexpression with loose bound variables: {v}"
  return .app (.lam `x (← inferType v) b .default) v

def letAbstractAux (pos : List Nat) (e : Expr) : MetaM Expr := do
  let (b, v) ← AbstractAux 0 pos e
  if v.hasLooseBVars then throwError m! "cannot let-abstract a subexpression with loose bound variables: {v}"
  return mkLet `x (← inferType v) v b

def betaAbstract (pos abstractPos : List Nat) (_tree : Expr) : MetaM (Option String) := do
  let rec takePrefix {α : Type} [BEq α] : List α → List α → Option (List α)
    | [], xs => some xs
    | _ , [] => none
    | x::xs, y::ys => if x == y then takePrefix xs ys else none
  let some pos' := takePrefix pos abstractPos | return none
  return s! "beta_abstract {pos} {pos'}"

elab "beta_abstract" pos:treePos pos':treePos : tactic => do
  let pos := getPosition pos
  let pos' := getPosition pos'
  workOnTreeDefEq (edit pos (betaAbstractAux pos'))

example : (fun x => x) 1 = 1 := by
  beta_abstract [1] []
  rfl
