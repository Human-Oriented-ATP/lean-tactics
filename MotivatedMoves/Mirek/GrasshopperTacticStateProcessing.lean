-- import Lean.Widget
-- import ProofWidgets
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Init.Classical
import Mathlib.Tactic
import MotivatedMoves.Mirek.UncurriedAppDelab

abbrev Jump := PNat
abbrev MineField := List Bool
abbrev Jumps := List Jump
abbrev JumpSet := Multiset Jump

abbrev Jumps.length (jumps : Jumps) := List.length jumps
abbrev MineField.length (mineField : MineField) := List.length mineField
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

section Auto

open Lean Elab Qq Meta Tactic

set_option pp.funBinderTypes true
set_option pp.tagAppFns true
set_option pp.analyze.typeAscriptions true
set_option pp.proofs.withType false
set_option pp.notation false
set_option pp.coercions false

-- abbrev Qq.Quoted.render {α : Q(Type $u)} (e : Q($α)) : MetaM String := do
def Expr.render (e : Expr) : MetaM String :=
  let options : Options :=
    (.empty : Options)
    |>.insert `pp.funBinderTypes true
    |>.insert `pp.tagAppFns true
    |>.insert `pp.analyze.typeAscriptions true
    |>.insert `pp.proofs.withType false
    |>.insert `pp.notation false
    |>.insert `pp.coercions false
  withOptions (options.mergeBy fun _ opt _ ↦ opt) <| do
    return toString (← ppExpr e)

partial def Expr.exportTheorem : Q(Prop) → TacticM String
  | ~q($P ∧ $Q) => return s!"AND({← exportTheorem P}, {← exportTheorem Q})"
  | ~q($P ∨ $Q) => return s!"OR({← exportTheorem P}, {← exportTheorem Q})"
  | ~q(¬$P) => return s!"NOT({← exportTheorem P})"
  | ~q((($P) : Prop) → $Q) => return s!"IMPLIES({← exportTheorem P}, {← exportTheorem Q})"
  | ~q(∃ (a : $α), $P a) =>
      withLocalDeclQ `a .default α fun var ↦ do
      return s!"EXISTS({"a"}, {← Expr.render α}, {← exportTheorem q($P $var)}"
  | e@(.forallE _ _ _ _) =>
    Meta.forallTelescope e fun args body ↦ do
      let proofArgs ← args.filterM fun arg ↦ do isProp (← inferType arg)
      let termArgs ← args.filterM fun arg ↦ do return !(← isProp (← inferType arg))
      let termArgs ← termArgs.mapM fun arg ↦ do return s!"{(← arg.fvarId!.getUserName).getRoot} : {← (Expr.exportTheorem <| ← inferType arg)}"
      let propBody ← mkForallFVars proofArgs body
      return s!"{termArgs |>.toList |>.intersperse "," |> String.join} :: {← Expr.exportTheorem propBody}"
  | ~q(@Eq ($α : Type) $x $y) => return s!"EQUALS({← Expr.render x}, {← Expr.render y})"
  | ~q(@LT.lt ($α : Type) (_ : LT $α) $a $b) => return s!"LT({← Expr.render a}, {← Expr.render b})"
  | ~q(@LE.le ($α : Type) (_ : LE $α) $a $b) => return s!"LE({← Expr.render a}, {← Expr.render b})"
  | e => Expr.render e

elab "auto" fileName?:(str)? : tactic => do
  evalTactic <| ← `(tactic| by_contra) -- negating the goal and adding it as a hypothesis
  evalTactic <| ← `(tactic| simp only [not_imp, not_and, not_forall, not_exists, not_not, not_true, not_false_iff, not_le, not_lt] at *)
  withMainContext do
    let forbidden := #[`_example, `grasshopper_ih]
    let localDecls := (← getLCtx).decls.toArray.filterMap id |>.filter fun decl ↦ !(decl.kind == .implDetail || forbidden.contains decl.userName.getRoot)
    let context : Array String ← localDecls.filterMapM fun decl ↦ do
      if ← isProp decl.type then
        return none
      else
        return s!"{decl.userName.getRoot.toString} : {← Expr.render decl.type}"
    -- logInfo m!"Local context: {context}"
    let hypotheses : Array String ← localDecls.filterMapM fun decl ↦ do
      if (← isProp decl.type) && !forbidden.contains decl.userName.getRoot then
        -- logInfo s!"Local hypothesis: {decl.userName.getRoot}"
        Expr.exportTheorem decl.type
      else return none
    -- logInfo m!"Hypotheses: {hypotheses}"
    let output : String := (context ++ #["\n---"] ++ hypotheses)
      |>.map (String.push · '\n') |>.foldl (init := "") String.append
    logInfo output
    if let some fileName := fileName? then
      IO.FS.writeFile fileName.getString output
    evalTactic <| ← `(tactic| sorry)

end Auto


section Theorems

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
    mines = mines0 ++ singleton true ++ mines1 ∧
    mines0.countMines = 0
  := by sorry

  theorem split_jump_landings
    (jumps : Jumps) (i : Int)
    (_ : i >= 0 := by auto)
    (_ : i < jumps.sum := by auto)
  : ∃ (jumps0 : Jumps) (j : Jump) (jumps1 : Jumps),
    jumps = jumps0 ++ singleton j ++ jumps1 ∧
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
    (∀ x : ℤ, mines1.getIndexD x → mines.getIndexD x) ∧
    (∀ x : ℤ, mines2.getIndexD x → mines.getIndexD x) ∧
    mines.countMines <= mines1.countMines + mines2.countMines
  := by sorry

end Theorems

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
    (∀ (x : ℤ), ¬jumps_ih.landings.getIndexD x ∨ ¬mines.getIndexD x)
  ) :
  main_jumps.Nodup →
  main_jumps.sum = main_mines.length+1 →
  main_jumps.sizeOf > main_mines.countMines →
  ∃ (jumpso : Jumps),
  main_jumps = jumpso.s ∧
  (∀ (x : ℤ), ¬jumpso.landings.getIndexD x ∨ ¬main_mines.getIndexD x)
:= by
  intros
  by_cases main_mines.countMines = 0
  -- mines are nonempty
  · let ⟨jumpso, _⟩ := order_jumps main_jumps
    use jumpso
    clear grasshopper_ih
    refine' ⟨_, _⟩
    · auto
    · intro x
      auto
  -- no mine on the first jump
  · let ⟨J, jumps, _, _⟩ := pop_max_jump main_jumps
    let ⟨mines0, mines1, _, _⟩ := split_mines main_mines J.length
    let ⟨mines00, mines01, _, _⟩ := split_mines main_mines (J.length-1)
    by_cases ¬ mines01.getIndexD 0
    · by_cases mines0.countMines ≠ 0
      -- mine before the first jump
      · let ⟨jumpso, _, _⟩ := grasshopper_ih jumps mines1 (by auto) (by auto) (by auto) (by auto)
        use (singleton J : Jumps) ++ jumpso
        refine' ⟨_, _⟩
        · auto
        · intro x
          auto
      -- no mine before the first jump
      · let ⟨mines10, mines11, _, _⟩ := split_first_mine mines1
        let ⟨jumpso, _, _⟩ := grasshopper_ih jumps (mines10 ++ singleton false ++ mines11) (by auto) (by auto) (by auto) (by auto)
        by_cases ¬ jumpso.landings.getIndexD mines10.length
        -- no landing at the removed mine
        · use singleton J ++ jumpso
          refine' ⟨_, _⟩
          · auto
          · intro x
            auto
        -- landing at the removed mine
        · let ⟨jumps0, J2, jumps1, _, _⟩ := split_jump_landings jumpso (mines10.length+1)
          use jumps0 ++ singleton J2 ++ singleton J ++ jumps1
          refine' ⟨_, _⟩
          · auto
          · intro x
            auto
    -- mine on the first jump
    · by_cases mines00.length <= mines1.length
      -- the first segment is smaller than the rest
      · let ⟨mines10, mines11, _, _⟩ := split_mines mines1 mines00.length
        let ⟨mines_un, _, _, _, _, _, _, _⟩ := union_mines mines00 mines10
        let ⟨jumpso, _, _⟩ := grasshopper_ih jumps (mines_un ++ mines11) (by auto) (by auto) (by auto) (by auto)
        let ⟨J2, jumpso, _⟩ := pop_first_jump jumpso
        use singleton J2 ++ singleton J ++ jumpso
        refine' ⟨_, _⟩
        · auto
        · intro x
          auto
      -- the first segment is bigger than the rest
      · let ⟨mines00, _, _, _⟩ := split_mines mines00 mines1.length
        let ⟨mines_un, _, _, _, _, _, _, _⟩ := union_mines mines00 mines1
        let ⟨jumpso, _, _⟩ := grasshopper_ih jumps mines_un (by auto) (by auto) (by auto) (by auto)
        let ⟨J2, jumpso, _⟩ := pop_first_jump jumpso
        use singleton J2 ++ singleton J ++ jumpso
        refine' ⟨_, _⟩
        · auto
        · intro x
          auto
