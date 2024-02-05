import Lean.Widget
import ProofWidgets
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

def Finset.shiftR.{u} {α : Type u} [AddCancelMonoid α]
  (s : Finset α) (i : α) : Finset α :=
  Finset.map ⟨λ x ↦ x+i, λ x y ↦ AddCancelMonoid.add_right_cancel x i y⟩ s
def Finset.shiftL.{u} {α : Type u} [AddGroup α]
  (s : Finset α) (i : α) : Finset α :=
  Finset.shiftR s (-i)

open Lean

structure GrasshopperPermProps where
  jumps : List String
deriving ToJson, FromJson
structure GrasshopperFixedProps where
  jumps : List Nat
deriving ToJson, FromJson

open ProofWidgets in
@[widget_module]
def GrasshopperPerm : Component GrasshopperPermProps where
  javascript := include_str ".." / ".." / "build" / "js" / "grasshopperPerm.js"
open ProofWidgets in
@[widget_module]
def GrasshopperFixed : Component GrasshopperFixedProps where
  javascript := include_str ".." / ".." / "build" / "js" / "grasshopperFixed.js"

open ProofWidgets.Jsx in
#html <GrasshopperPerm jumps={["x1","x2","x3","x4"]} />
open ProofWidgets.Jsx in
#html <GrasshopperFixed jumps={[2,4]} />

structure Minefield where
  left : Int
  right : Int
  mines : Finset Int
  left_right : left ≤ right
  left_mines : ∀ mine ∈ mines, (left < mine)
  mines_right : ∀ mine ∈ mines, (mine < right)

def Minefield.length (m : Minefield) : Int := m.right - m.left
def Minefield.num_mines (m : Minefield) : Int := m.mines.card
def Minefield.hasMine (m : Minefield) (mine : Int) : Prop := mine ∈ m.mines

#check Finset.filter

def Minefield.leftPart (m : Minefield) (right : Int)
  (h : m.left ≤ right) : Minefield :=
  {
    left := m.left
    right := right
    mines := m.mines.filter (λ mine ↦ mine < right)
    left_right := h
    left_mines := by
      intro mine
      intro this
      have : mine ∈ m.mines := (Finset.mem_filter.1 this).1
      exact m.left_mines mine this
    mines_right := by
      intro mine
      intro this
      exact (Finset.mem_filter.1 this).2
  }
def Minefield.rightPart (m : Minefield) (left : Int)
  (h : left ≤ m.right) : Minefield :=
  {
    left := left
    right := m.right
    mines := m.mines.filter (λ mine ↦ left < mine)
    left_right := h
    left_mines := by
      intro mine
      intro this
      exact (Finset.mem_filter.1 this).2
    mines_right := by
      intro mine
      intro this
      have : mine ∈ m.mines := (Finset.mem_filter.1 this).1
      exact m.mines_right mine this
  }

def Minefield.union (m1 m2 : Minefield) : Minefield :=
  {
    left := min m1.left m2.left
    right := max m1.right m2.right
    mines := m1.mines ∪ m2.mines
    left_right := by
      calc min m1.left m2.left ≤ m1.left    := Int.min_le_left m1.left m2.left
           m1.left ≤ m1.right               := m1.left_right
           m1.right ≤ max m1.right m2.right := Int.le_max_left m1.right m2.right
    left_mines := by
      intro mine hin
      apply (Finset.mem_union.mp hin).elim; {
        intro hin
        calc min m1.left m2.left ≤ m1.left := Int.min_le_left m1.left m2.left
             m1.left < mine := m1.left_mines mine hin
      }; {
        intro hin
        calc min m1.left m2.left ≤ m2.left := Int.min_le_right m1.left m2.left
             m2.left < mine := m2.left_mines mine hin
      }
    mines_right := by
      intro mine hin
      apply (Finset.mem_union.mp hin).elim; {
        intro hin
        calc mine < m1.right := m1.mines_right mine hin
             m1.right ≤ max m1.right m2.right := Int.le_max_left m1.right m2.right
      }; {
        intro hin
        calc mine < m2.right := m2.mines_right mine hin
             m2.right ≤ max m1.right m2.right := Int.le_max_right m1.right m2.right
      }
  }

def Minefield.join (m1 m2 : Minefield) (h : m1.right = m2.left+1) (left_right : m1.left ≤ m2.right) : Minefield :=
  {
    left := m1.left
    right := m2.right
    mines := m1.mines ∪ m2.mines
    left_right := left_right
    left_mines := sorry
    mines_right := sorry
  }

def Minefield.shiftR (m : Minefield) (i : Int) : Minefield :=
  {
    left := m.left+i
    right := m.right+i
    mines := m.mines.shiftR i
    left_right := sorry
    left_mines := sorry
    mines_right := sorry
  }
def Minefield.shiftL (m : Minefield) (i : Int) : Minefield :=
  Minefield.shiftR m (-i)

abbrev PInt := {x : Int // x > 0}
def UJumps := Multiset PInt

def UJumps.ijumps (uJumps : UJumps) : Multiset Int := Multiset.map Subtype.val uJumps
def UJumps.length (uJumps : UJumps) := uJumps.ijumps.sum
def UJumps.num (uJumps : UJumps) := Multiset.card uJumps

structure Jumping where
  jumps : List PInt
  left : Int

#check Multiset

def Jumping.iJumps (jumping : Jumping) : List Int :=
  jumping.jumps.map Subtype.val
def Jumping.uJumps (jumping : Jumping) : UJumps :=
  Multiset.ofList jumping.jumps
def Jumping.right (jumping : Jumping) : Int :=
  jumping.left + jumping.iJumps.sum

def Jumping.shiftR (jumping : Jumping) (i : Int) : Jumping := {
  jumps := jumping.jumps
  left := jumping.left+i
}
def Jumping.shiftL (jumping : Jumping) (i : Int) : Jumping :=
  jumping.shiftR (-i)

def List.cumsum.{u} {α : Type u} [Add α] [Zero α] : List α → List α
| [] => []
| a::t => Zero.zero::((List.cumsum t).map (Add.add a))

def Jumping.landings (jumping : Jumping) : Finset Int
  := jumping.iJumps.cumsum.tail.toFinset

def Jumping.valid_on (jumping : Jumping) (minefield : Minefield) : Prop :=
  jumping.left = minefield.left ∧ jumping.right = minefield.right
def Jumping.succeeds_on (jumping : Jumping) (minefield : Minefield) : Prop :=
  Disjoint jumping.landings minefield.mines

def SetInt.popGeneral
  (getter : Finset Int → Option Int)
  (of_nonempty : ∀ {s : Finset Int}, s.Nonempty → ∃ a : Int, getter s = a)
  (s : SetInt) (h : s.size > 0) : Int × SetInt :=
  let res := getter s
  have is_some : ∃x, res = some x :=
    Int.ofNat_pos.mp h |> Finset.card_pos.mp |> of_nonempty
  match res with
  | some m => (m, s.erase m)
  | none => False.elim (is_some.elim (λ _ h2 => Option.noConfusion h2))


@[simp]
def grasshopper_assump (uJumps : UJumps) (minefield : Minefield) :=
  uJumps.length = minefield.length ∧ uJumps.num > minefield.num_mines

@[simp]
def grasshopper_goal (uJumps : UJumps) (minefield : Minefield) (jumping : Jumping) :=
  jumping.uJumps = uJumps ∧
  jumping.valid_on minefield ∧
  jumping.succeeds_on minefield

def grasshopper :
  ∀ (uJumps : UJumps) (minefield : Minefield),
    grasshopper_assump uJumps minefield →
    ∃ jumping : Jumping,
      grasshopper_goal uJumps minefield jumping := sorry

def grasshopper_with_ih
  (uJumps : UJumps)
  (minefield : Minefield)
  (assump : grasshopper_assump uJumps minefield)
  (ih : ∀ (uJumps2 : UJumps) (minefield2 : Minefield),
    uJumps2.num < uJumps.num →
    grasshopper_assump uJumps2 minefield2 →
    ∃ jumping2 : Jumping,
      grasshopper_goal uJumps2 minefield2 jumping2
  ) :
  ∃ jumping : Jumping,
      grasshopper_goal uJumps minefield jumping :=
by
  sorry

noncomputable
def skolem1 {α β : Type} {p : α → Prop} {q : β → Prop} [Inhabited β]
  (f : ∀ x : α, p x → ∃ y : β, q y) (arg : α) : β :=
  match Classical.dec (p arg) with
  | isTrue h => Exists.choose (f arg h)
  | isFalse _ => default

#check skolem1

theorem skolem1_thm {α β : Type} {p : α → Prop} {q : β → Prop} [Inhabited β]
  (f : ∀ x : α, p x → ∃ y : β, q y) (arg : α) (h : p arg)
  : q (skolem1 f arg) := by unfold skolem1; exact (
    match Classical.dec (p arg) with
    | isTrue h => Exists.choose_spec (f arg h)
    | isFalse nh => (nh h).elim
  )

#print skolem1_thm

example (jumps : ListNat) (mines : SetInt)
  (assump : grasshopper_assump (jumps, mines))
  (ih : ∀ (args : ListNat × SetInt),
    let (jumps2, mines2) := args
    jumps2.size < jumps.size ∧
    grasshopper_assump (jumps2, mines2)
    →
    ∃ jumps_ord : ListNat, (grasshopper_goal (jumps, mines, jumps_ord))
  )
  : ∃ jumps_ord : ListNat, (grasshopper_goal (jumps, mines, jumps_ord))
  := by
  -- initial steps
  by_contra ngoal
  simp only [grasshopper_goal, grasshopper_assump] at *
  push_neg at ngoal
  -- try_small1
  -- try_small2
  -- take_any (jump : Nat) (jump ∈ jumps)
  let jump : Int := sorry
  let rest := jumps.pop jump sorry
  let (mines0,mines1) := mines.split (jump+1)
  let rest_ord := skolem1 ih (rest, mines1.shiftL jump)
  --   assumed: mines1.size < jumps.size
  -- finish ngoal jump::rest_ord
  --   goal: (mines0 | mines1).disjoint (jump::rest_ord).cumsum
  --   simp: jump ∉ mines ∨ mines.disjoint
  --   assumed: jump ∉ mines


example (x1 x2 x3 : Nat) : x1 > 0 → x2 > 0 → x3 > 0 →
  x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 → Finset.card { x1, x1+x3, x2, x2+x3 } <= 2
  → False := by
  intros
  sorry

-- set_option profiler true
lemma grass (x1 x2 x3 : Nat) : 0 < x1 → 0 < x2 → 0 < x3 →
  x1 < x2 ∨ x1 > x2 →
  x1 < x3 ∨ x1 > x3 →
  x2 < x3 ∨ x2 > x3 →
  Finset.card { x1 } = 1 →
  Finset.card { x1 } <= Finset.card { x1, x1+x3 } →
  Finset.card { x1, x1+x3 } <= Finset.card { x1, x1+x3, x2 } →
  Finset.card { x1, x1+x3, x2 } <= Finset.card { x1, x1+x3, x2, x2+x3 } →
  Finset.card { x1 } + 1 = Finset.card { x1, x1+x3 } ∨ x1+x3 = x1 →
  Finset.card { x1, x1+x3 } + 1 = Finset.card { x1, x1+x3, x2 } ∨ x2 = x1+x3 ∨ x2 = x1 →
  Finset.card { x1, x1+x3, x2 } + 1 = Finset.card { x1, x1+x3, x2, x2+x3 } ∨ x2+x3 = x2 ∨ x2+x3 = x1+x3 ∨ x2+x3 = x1 →
  Finset.card { x1, x1+x3, x2, x2+x3 } <= 2 →
  False := by
  intros
  omega

-- #print grass
#check Finset.map
