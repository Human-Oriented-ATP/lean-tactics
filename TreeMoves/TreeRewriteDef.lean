import TreeMoves.Tree

namespace Tree

open Lean Meta

def rewriteDef (goalPos : List Nat) (tree : Expr) : MetaM (Option (Expr × AssocList SubExpr.Pos Widget.DiffTag × String)) := 
  withTreeSubexpr tree goalPos fun _pol e => do
    let some name := e.getAppFn.constName? | return none
    let .defnInfo info ← getConstInfo name | return none
    lambdaTelescope info.value fun xs body => do
      let lhs := mkAppN (.const info.name <| info.levelParams.map mkLevelParam) xs
      let type ← mkForallFVars xs (← mkEq lhs body)
      let lhsPos := SubExpr.Pos.ofArray $ (Array.mkArray (xs.size * 2) 1).push 0 |>.push 1
      let rhsPos := SubExpr.Pos.ofArray $ (Array.mkArray (xs.size * 2) 1).push 1
      let diffs := AssocList.nil.cons lhsPos .willChange |>.cons rhsPos .wasChanged
      let move := s! "tree_rewrite_def {goalPos}"
      return some (type, diffs, move)

def replaceByDef (e : Expr) : MetaM Expr :=
  Expr.withAppRev e fun f revArgs => do
    let .const name us := f | throwError "head of expression is not a constant {indentExpr f}"
    let info ← getConstInfoDefn name
    let value := info.value.instantiateLevelParams info.levelParams us
    return value.betaRev revArgs

def editTree [Monad m] [MonadError m] (edit : Expr → m Expr) : List TreeBinderKind → Expr → m Expr
  | .all ::xs, forall_pattern   n u d tree => return mkForall n u d (← editTree edit xs tree)
  | .ex  ::xs, exists_pattern   n u d tree => return mkExists n u d (← editTree edit xs tree)
  | .inst::xs, instance_pattern n u d tree => return mkInstance n u d (← editTree edit xs tree)
  | .imp_right::xs, imp_pattern p tree => return mkImp p (← editTree edit xs tree)
  | .imp_left ::xs, imp_pattern tree p => return mkImp (← editTree edit xs tree) p
  | .and_right::xs, and_pattern p tree => return mkAnd p (← editTree edit xs tree)
  | .and_left ::xs, and_pattern tree p => return mkAnd (← editTree edit xs tree) p
  | [], e => edit e
  | xs, e => throwError m! "could not find position {xs} in {indentExpr e}"

def editExpr [Monad m] [MonadError m] (edit : Expr → m Expr) : List Nat → Expr → m Expr
  | xs   , .mdata d b        => return .mdata d (← editExpr edit xs b)
  
  | 0::xs, .app f a          => return .app (← editExpr edit xs f) a
  | 1::xs, .app f a          => return .app f (← editExpr edit xs a)

  | 0::xs, .proj n i b       => return .proj n i (← editExpr edit xs b)

  | 0::xs, .letE n t v b d   => return .letE n (← editExpr edit xs t) v b d
  | 1::xs, .letE n t v b d   => return .letE n t (← editExpr edit xs v) b d
  | 2::xs, .letE n t v b d   => return .letE n t v (← editExpr edit xs b) d
                                                    
  | 0::xs, .lam n t b bi     => return .lam n (← editExpr edit xs t) b bi
  | 1::xs, .lam n t b bi     => return .lam n t (← editExpr edit xs b) bi

  | 0::xs, .forallE n t b bi => return .forallE n (← editExpr edit xs t) b bi
  | 1::xs, .forallE n t b bi => return .forallE n t (← editExpr edit xs b) bi

  | []   , e                 => edit e
  | list, e                  => throwError m!"could not find subexpression {list} in '{e}'"


open Lean Elab.Tactic in

elab "tree_rewrite_def" pos:treePos : tactic => do
  let pos := getPosition pos
  let tree ← getMainTarget
  let (path, pos) := posToPath pos tree
  let newTree ← liftMetaM $ editTree (editExpr (replaceByDef) pos) path tree
  replaceMainGoal [← (← getMainGoal).change newTree]

example : ∀ n:Nat, n + n = 2*n := by
  make_tree
  tree_rewrite_def [1,1]
  tree_rewrite_def [1,0,1]
  tree_rewrite_def [1,0,1,0,0,0]
  sorry

example : ∀ n:Nat, Prod.fst (n,n) = n := by
  make_tree
  tree_rewrite_def [1,0,1]
  sorry
