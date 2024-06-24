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
abbrev Jumps.length (jumps : Jumps) := List.length jumps
abbrev MineField.length (mineField : MineField) := List.length mineField

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

macro "auto" : tactic => `(tactic | sorry)

theorem order_jumps
: ∀ jumps : JumpSet,
  ∃ jumpso : Jumps,
  jumps = jumpso.s
:= by sorry

theorem pop_max_jump
  (jumps : JumpSet)
  (_ : jumps.sizeOf > 0 := by auto)
: ∃ (j : Jump) (jumpsr : JumpSet),
  jumps = .cons j jumpsr ∧
  (∀ x ∈ jumps, x.length <= j.length)
:= by sorry

theorem pop_first_jump
  (jumps : Jumps)
  (_ : jumps.length > 0 := by auto)
: ∃ (j : Jump) (jumpsr : Jumps),
  jumps = .cons j jumpsr
:= by sorry

theorem split_mines
  (mines : MineField) (i : ℤ)
  (_ : i >= 0 := by auto)
  (_ : i <= mines.length := by auto)
: ∃ (mines0 mines1 : MineField),
  mines = mines0 ++ mines1 ∧
  mines0.length = i
:= by sorry

theorem split_first_mine
  (mines : MineField)
  (_ : mines.countMines > 0 := by auto)
: ∃ (mines0 mines1 : MineField),
  mines = mines0 ++ [true] ++ mines1 ∧
  mines0.countMines = 0
:= by sorry

theorem split_jump_landings
  (jumps : Jumps) (i : Int)
  (_ : i >= 0 := by auto)
  (_ : i < jumps.sum := by auto)
: ∃ (jumps0 : Jumps) (j : Jump) (jumps1 : Jumps),
  jumps = jumps0 ++ [j] ++ jumps1 ∧
  jumps0.sum <= i ∧
  jumps0.sum + j.length > i
:= by sorry

theorem union_mines
  (mines1 mines2 : MineField)
  (_ : mines1.length = mines2.length := by auto)
: ∃ (mines : MineField),
  mines1.length = mines.length ∧
  mines2.length = mines.length ∧
  mines1.countMines <= mines.countMines ∧
  mines2.countMines <= mines.countMines ∧
  (∀ x : ℤ, mines1[x] → mines[x]) ∧
  (∀ x : ℤ, mines2[x] → mines[x]) ∧
  mines.countMines <= mines1.countMines + mines2.countMines
:= by sorry

example
  (main_jumps : JumpSet)
  (main_mines : MineField)
  (grasshopper_ih
  : ∀ (jumps : JumpSet) (mines : MineField),
    jumps.sizeOf < main_jumps.sizeOf →
    jumps.Nodup →
    jumps.sum = mines.length+1 →
    jumps.sizeOf > mines.countMines →
    ∃ (jumps_ih : Jumps),
    jumps = jumps_ih.s ∧
    (∀ (x : ℤ), ¬jumps_ih.landings[x] ∨ ¬mines[x])
  ) :
  main_jumps.Nodup →
  main_jumps.sum = main_mines.length+1 →
  main_jumps.sizeOf > main_mines.countMines →
  ∃ (jumpso : Jumps),
  main_jumps = jumpso.s ∧
  (∀ (x : ℤ), ¬jumpso.landings[x] ∨ ¬main_mines[x])
:= by
  intros
  by_cases main_mines.countMines = 0
  -- mines are nonempty
  · let ⟨jumpso, _⟩ := order_jumps main_jumps
    use jumpso
    auto
  -- no mine on the first jump
  · let ⟨J, jumps, _⟩ := pop_max_jump main_jumps
    let ⟨mines0, mines1, _⟩ := split_mines main_mines J.length
    let ⟨mines00, mines01, _⟩ := split_mines mines0 (J.length-1)
    by_cases ¬ mines01.getIndexD 0
    · by_cases mines0.countMines ≠ 0
      -- mine before the first jump
      · let ⟨jumpso, _⟩ := grasshopper_ih jumps mines1 (by auto) (by auto) (by auto) (by auto)
        use [J] ++ jumpso
        auto
      -- no mine before the first jump
      · let ⟨mines10, mines11, _⟩ := split_first_mine mines1
        let ⟨jumpso, _⟩ := grasshopper_ih jumps (mines10 ++ [false] ++ mines11) (by auto) (by auto) (by auto) (by auto)
        by_cases ¬ jumpso.landings.getIndexD mines10.length
        -- no landing at the removed mine
        · use [J] ++ jumpso
          auto
        -- landing at the removed mine
        · let ⟨jumps0, J2, jumps1, _⟩ := split_jump_landings jumpso (mines10.length+1)
          use jumps0 ++ [J2] ++ [J] ++ jumps1
          auto
    -- mine on the first jump
    · by_cases mines00.length <= mines1.length
      -- the first segment is smaller than the rest
      · let ⟨mines10, mines11, _⟩ := split_mines mines1 mines00.length
        let ⟨mines_un, _⟩ := union_mines mines00 mines10
        let ⟨jumpso, _⟩ := grasshopper_ih jumps (mines_un ++ mines11) (by auto) (by auto) (by auto) (by auto)
        let ⟨J2, jumpso, _⟩ := pop_first_jump jumpso
        use [J2] ++ [J] ++ jumpso
        auto
      -- the first segment is bigger than the rest
      · let ⟨mines00, _, _⟩ := split_mines mines00 mines1.length
        let ⟨mines_un, _⟩ := union_mines mines00 mines1
        let ⟨jumpso, _⟩ := grasshopper_ih jumps mines_un (by auto) (by auto) (by auto) (by auto)
        let ⟨J2, jumpso, _⟩ := pop_first_jump jumpso
        use [J2] ++ [J] ++ jumpso
        auto
