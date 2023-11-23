import MotivatedMoves.ProofState.TreeLemmas

namespace Tree

open Lean

abbrev InnerPosition := List ℕ
abbrev OuterPosition := List ℕ

def badInnerPositionMessage (e : Expr) (pos : InnerPosition) : MessageData := 
  m! "Could not find inner position {pos} in target {e}"
def badOuterPositionMessage (e : Expr) (pos : OuterPosition) : MessageData := 
  m! "Could not find outer position {pos} in target {e}"

def splitPosition (pos : List ℕ) : OuterPosition × InnerPosition :=
  splitAt2 pos
where
  splitAt2 : List ℕ → OuterPosition × InnerPosition
  | x::xs => if x == 2 then ([], xs) else Bifunctor.fst (x::·) $ splitAt2 xs
  | [] => ([],[])

def printPosition (outer : OuterPosition) (inner : InnerPosition) : String :=
  if inner == [] then s! "{outer}"
  else s! "{outer ++ 2 :: inner}" 

syntax treePos := "[" num,* "]"

def getPosition (stx : TSyntax `Tree.treePos) : List ℕ :=
  (stx.raw[1].getSepArgs.map (·.isNatLit?.getD 0)).toList

def getOuterInnerPosition (stx : TSyntax `Tree.treePos) : OuterPosition × InnerPosition := 
  splitPosition (getPosition stx)
