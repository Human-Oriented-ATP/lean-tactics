import Lean.Widget
import ProofWidgets

open Lean

structure SatLiteral where
  v : String
  pos : Bool := true
deriving ToJson, FromJson

instance : Neg SatLiteral where
  neg l := {v := l.v, pos := ¬l.pos}
instance : ToString SatLiteral where
  toString x := if x.pos then x.v else "¬"++x.v

def SatClause := List SatLiteral
deriving ToJson, FromJson

structure InteractiveCDCL.Props where
  startClauses : List SatClause
deriving ToJson, FromJson

open ProofWidgets in
@[widget_module]
def InteractiveCDCL : Component InteractiveCDCL.Props where
  javascript := include_str ".." / ".." / "build" / "js" / "cdcl.js"

def A := SatLiteral.mk "A" true
def B := SatLiteral.mk "B" true
def C := SatLiteral.mk "C" true
def D := SatLiteral.mk "D" true
def E := SatLiteral.mk "E" true

def clauses := [
  [A,B],
  [A,-B],
  [-A,B],
  [-A,-B],
  [C,B],
  [-C,B],
]

open ProofWidgets.Jsx in
#html <InteractiveCDCL startClauses={clauses}/>

def BuildSatM := StateM (List SatClause)
deriving Monad, MonadState

def add_constraint (c : SatClause) : BuildSatM Unit :=
  modifyGet (fun constraints => ((), c::constraints))
def BuildSatM.calc (code : BuildSatM Unit) :=
  let (_, constraints) := code.run []
  constraints.reverse

def or_or_implies_or (pair1 pair2 pair3 : SatLiteral × SatLiteral) : BuildSatM Unit := do
  let (a1,b1) := pair1
  let (a2,b2) := pair2
  let (a3,b3) := pair3
  add_constraint [-a1, -a2, a3, b3]
  add_constraint [-a1, -b2, a3, b3]
  add_constraint [-b1, -a2, a3, b3]
  add_constraint [-b1, -b2, a3, b3]

def or_tree_level_lits (n : Nat) : List (SatLiteral × SatLiteral) :=
  (List.range (n+1)).map λ i ↦ ({v := s!"A{n}_{i}" }, {v := s!"B{n}_{i}" })

def or_tree_aux (n : Nat) : BuildSatM Unit
  := match n with
| 0 => match or_tree_level_lits 0 with
  | [(l1,l2)] => do
    add_constraint [-l1]
    add_constraint [-l2]
  | _ => return
| n+1 => do
  let lits1 := or_tree_level_lits (n+1)
  let lits2 := lits1.tailD lits1
  let lits3 := or_tree_level_lits n
  for (pair1,pair2,pair3) in lits1.zip (lits2.zip lits3) do
    or_or_implies_or pair1 pair2 pair3
  or_tree_aux n

def or_tree (n : Nat) : BuildSatM Unit := do
  for (a,b) in or_tree_level_lits n do
    add_constraint [a,b]
  or_tree_aux n

open ProofWidgets.Jsx in
#html <InteractiveCDCL startClauses={(or_tree 3).calc}/>

open ProofWidgets.Jsx in
#html <InteractiveCDCL startClauses={(or_tree 10).calc}/>

def at_most_one (lits : List SatLiteral) : BuildSatM Unit :=
  match lits with
  | [] => return
  | hd::tl => do
    for l in tl do
      add_constraint [-hd, -l]
    at_most_one tl

def exactly_one (lits : List SatLiteral) : BuildSatM Unit := do
  add_constraint lits
  at_most_one lits

namespace Sudoku
def table : List (List (List SatLiteral)) := (List.range 9).map (fun y =>
  (List.range 9).map (fun x =>
    (List.range 9).map (fun el =>
      { v := s!"a{y+1}{x+1} = {el+1}" }
    )
  )
)

def unique_nums (squares : List (List SatLiteral)) : BuildSatM Unit := do
  for el in List.range 9 do
    exactly_one (squares.filterMap fun sq => sq[el]?)
def glob_constraints : BuildSatM Unit := do
  for row in table do
    for sq in row do
      exactly_one sq
  for row in table do
    unique_nums row
  for coli in List.range 9 do
    unique_nums (table.filterMap fun row => row[coli]?)
  for starty in [0,3,6] do
    for startx in [0,3,6] do
      let bigSquare := table.drop starty |>.take 3 |>.map (
        fun row => (row.drop startx |>.take 3))
      unique_nums (bigSquare.foldl List.append [])
def ini_constraints (iniTable : List (List Nat)) : BuildSatM Unit := do
  for (row, iniRow) in table.zip iniTable do
    for (sq, iniSq) in row.zip iniRow do
      if iniSq > 0 ∧ iniSq <= 9 then
        let some l := sq[iniSq-1]? | return
        add_constraint [l]

def constraints (iniTable : List (List Nat)) : List SatClause :=
  (do
    ini_constraints iniTable
    glob_constraints
  ).calc

end Sudoku

def sudoku1 := (let __ := 0; [
  [__, __, __,    4,  9, __,    2, __, __],
  [__, __,  6,   __,  1, __,   __,  4,  7],
  [__, __,  4,   __,  5, __,   __,  9, __],

  [ 6,  7, __,    5, __,  1,    4, __, __],
  [ 8, __, __,   __,  4, __,    7, __, __],
  [ 5,  4,  9,    8, __, __,    3, __,  6],

  [ 4,  1, __,    9,  6, __,    8, __, __],
  [__, __, __,    1, __,  5,    9, __,  4],
  [__,  2,  8,   __,  7, __,   __,  6,  5],
])

def sudoku2 := (let __ := 0; [
  [__, __,  1,    5, __,  6,   __, __, __],
  [ 5, __, __,   __, __, __,    2, __, __],
  [ 3, __, __,   __,  7,  9,   __, __, __],

  [__,  3, __,   __, __, __,    9, __,  4],
  [__, __,  5,   __,  8, __,    7, __, __],
  [ 7, __,  2,   __, __, __,   __,  5, __],

  [__, __, __,    9,  6, __,   __, __,  8],
  [__, __,  3,   __, __, __,   __, __,  1],
  [__, __, __,    7, __,  2,    4, __, __],
])

open ProofWidgets.Jsx in
#html <InteractiveCDCL startClauses={
  Sudoku.constraints sudoku1
}/>

open ProofWidgets.Jsx in
#html <InteractiveCDCL startClauses={
  Sudoku.constraints sudoku2
}/>
