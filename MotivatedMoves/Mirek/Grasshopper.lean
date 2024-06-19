import Lean.Widget
import ProofWidgets
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

abbrev Jump := PNat
abbrev MineField := List Bool
abbrev Jumps := List Jump
abbrev JumpSet := Multiset Jump

def Jump.length (j : Jump) : Int := j

def List.getIndexD [Inhabited α] (l : List α) (idx : Int) : α :=
  match idx with
  | .ofNat n => l.getD n default
  | .negSucc _ => default

instance [Inhabited α] : GetElem (List α) Int α (fun _ _ => True) where
  getElem l idx _ := List.getIndexD l idx

def x : Jumps := [2,5,3]
def JumpSet.sum (jumps : JumpSet) : Int := (jumps.map Jump.length).sum
def MineField.countMines (mines : MineField) : Int := mines.countP id

def jumpOver (j : Jump) : MineField := List.replicate j.natPred false
def Jumps.landings (jumps : Jumps) : MineField := jumps.bind (fun j => (jumpOver j).concat true)
def Jumps.s (jumps : Jumps) : JumpSet := .ofList jumps
def Jumps.sum (jumps : Jumps) : Int := jumps.s.sum

theorem order_jumps
: ∀ jumps : JumpSet,
  ∃ jumpso : Jumps,
  jumps = jumpso.s
:= by sorry

theorem pop_max_jump
: ∀ jumps : JumpSet,
  jumps.sizeOf > 0 →
  ∃ (j : Jump) (jumpsr : JumpSet),
  jumps = .cons j jumpsr ∧
  (∀ x ∈ jumps, x.length <= j.length)
:= by sorry

theorem pop_first_jump
: ∀ jumps : Jumps,
  jumps.length > 0 →
  ∃ (j : Jump) (jumpsr : Jumps),
  jumps = .cons j jumpsr
:= by sorry

theorem split_mines
: ∀ (mines : MineField) (i : ℤ),
  i >= 0 →
  i <= mines.length →
  ∃ (mines0 mines1 : MineField),
  mines = mines0 ++ mines1 ∧
  mines0.length = i
:= by sorry

theorem split_first_mine
: ∀ (mines : MineField),
  mines.countMines > 0 →
  ∃ (mines0 mines1 : MineField),
  mines = mines0 ++ [true] ++ mines1 ∧
  mines0.countMines = 0
:= by sorry

theorem split_jump_landings
: ∀ (jumps : Jumps),
  i >= 0 →
  i < jumps.sum →
  ∃ (j : Jump) (jumps0 jumps1 : Jumps),
  jumps = jumps0 ++ [j] ++ jumps1 ∧
  jumps0.sum <= i ∧
  jumps0.sum + j.length > i
:= by sorry

theorem union_mines
: ∀ (mines1 mines2 : MineField),
  mines1.length = mines2.length →
  ∃ (mines : MineField),
  mines1.length = mines.length ∧
  mines2.length = mines.length ∧
  mines1.countMines <= mines.countMines ∧
  mines2.countMines <= mines.countMines ∧
  (∀ x : ℤ, mines1[x] → mines[x]) ∧
  (∀ x : ℤ, mines2[x] → mines[x]) ∧
  mines.countMines <= mines1.countMines + mines2.countMines
:= by sorry

axiom main_jumps : Jumps
axiom main_mines : MineField

theorem grasshopper_ih
: ∀ (jumps : JumpSet) (mines : MineField),
  jumps.sizeOf < main_jumps.length →
  jumps.Nodup →
  jumps.sum = mines.length+1 →
  jumps.sizeOf > mines.countMines
:= by sorry
