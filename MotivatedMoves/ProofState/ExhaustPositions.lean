import MotivatedMoves.ProofState.Tree

open Lean MotivatedTree

def appendToAll (positions : Array OuterPosition) (head : Nat) : Array OuterPosition :=
  positions.map (fun xs => head :: xs)

partial def getInnerPositions (e : Expr) : MetaM (Array InnerPosition) := do
  match e with
  | .app fn arg =>
    let fnPositions ← getInnerPositions fn
    let argPositions ← getInnerPositions arg
    pure (appendToAll fnPositions 0 ++ appendToAll argPositions 1)

  | .lit ..
  | .const ..
  | .mvar ..
  | .bvar ..
  | .fvar ..
  | .sort .. => pure #[[]]

  | .mdata _ e => getInnerPositions e

  | .forallE .. => throwError "Cannot have .forallE in tree expression."

  | _ => throwError "Position case not implemented"

open Elab Tactic Meta

elab "inner_positions" : tactic => do
  let target ← getMainTarget
  let positions ← getInnerPositions target
  dbg_trace "{positions} \n {target}"

partial def getValidPositions (e : Expr) : MetaM (Array (List Nat)) := do
  match ← replaceForallE e with
  | instance_pattern n _ d b
  | forall_pattern n _ d b
  | exists_pattern n _ d b => withLocalDeclD n d fun fvar =>
    return appendToAll (← getValidPositions (b.instantiate1 fvar)) 1 ++ #[[]]

  | and_pattern  p q
  | imp_pattern  p q => do
      return appendToAll (← getValidPositions p) 1 ++ appendToAll (← getValidPositions q) 0 ++ #[[]]

  | e => pure $ appendToAll (← getInnerPositions e) 2

elab "positions" : tactic => do
  let target ← getMainTarget
  let positions ← getValidPositions target
  dbg_trace "Number of positions: {positions.size}"
  dbg_trace "{positions} \n {target}"
