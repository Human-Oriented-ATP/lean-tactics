import MotivatedMoves.Moves.TreeApply

namespace Tree

open Lean Meta Elab.Tactic

def getInductionPos (hyp : Expr) (_ : MetaM Bool) : MetaM (Expr × TreePos × Pos) := do
  let hypTree ← makeTree hyp
  let path := findTreePos hypTree
  return (← makeTreePath path hyp, path.take (path.length - 1), [])

elab "tree_induction" pos:treePos : tactic => do
  let (treePos, pos) := getSplitPosition pos
  (workOnTreeAt treePos fun pol tree => do
  unless pos == [] do
    throwError m! "cannot apply induction in a subexpression: position {pos} in {indentExpr tree}"
  match tree with
    | imp_pattern domain _
    | forall_pattern _ _ domain _ =>
      unless pol do
        throwError m! "cannot do induction in negative position"
      let domain ← whnfD domain
      matchConst domain.getAppFn
        (fun _ => throwError m! "expected an inductive type, not {indentExpr domain}")
        (fun cinfo _ => do
          let .inductInfo val := cinfo | throwError m! "expected an inductive type, not {indentExpr domain}"
          if val.all.length != 1 then
            throwError "'induction' move does not support mutually inductive types, the eliminator '{mkRecName val.name}' has multiple motives"
          if val.isNested then
            throwError "'induction' move does not support nested inductive types, the eliminator '{mkRecName val.name}' has multiple motives"
          
          let recName : Name := .str val.name (if val.name == `Nat then "recAux" else "rec")
          applyUnbound recName getInductionPos [] [] treeApply tree  )
    | _ => throwError m! "cannot apply induction at {tree}")
  workOnTreeDefEq makeTree
