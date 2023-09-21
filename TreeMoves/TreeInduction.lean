import TreeMoves.TreeApply

namespace Tree

open Lean Meta Elab.Tactic

def getInductionPos (hyp : Expr) (_goalPath : List TreeBinderKind) : MetaM (Expr × List TreeBinderKind × List Nat) := do
  let hypTree ← makeTree hyp
  let path := findPath hypTree
  return (← makeTreePath path hyp, path.take (path.length - 1), [])

elab "tree_induction" goalPos:treePos : tactic => do
  let goalPos := getPosition goalPos
  workOnTreeAt goalPos fun pos pol tree => do
  unless pos == [] do
    throwError m! "cannot apply induction in a subexpression: position {pos} in {indentExpr tree}"
  match tree with
  | imp_pattern domain _
  | forall_pattern _n _u domain _ =>
    if pol
    then do
    let domain ← whnfD domain
    matchConst domain.getAppFn
      (fun _ => throwError m! "type is not an inductive type {indentExpr domain}")
      (fun cinfo _ => do
        let .inductInfo val := cinfo | throwError m! "expected an inductive type {indentExpr domain}"
        if val.all.length != 1 then
          throwError "'induction' move does not support mutually inductive types, the eliminator '{mkRecName val.name}' has multiple motives"
        if val.isNested then
          throwError "'induction' move does not support nested inductive types, the eliminator '{mkRecName val.name}' has multiple motives"
        
        let recName : Name := .str val.name (if val.name == `Nat then "recAux" else "rec")
        applyUnbound recName getInductionPos [] treeApply tree
      )
    else
      throwError m! "cannot do induction in negative position"
        

  | _ => throwError m! "cannot apply induction at {tree}"
