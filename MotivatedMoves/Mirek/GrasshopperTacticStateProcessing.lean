import Lean
import Qq
import Mathlib.Tactic

open Lean Elab Qq Meta Tactic

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

def Expr.exportTerm : {α : Q(Type)} → Q($α) → MetaM String
  | ~q(Int), ~q(($a : Int) + ($b : Int)) => return s!"add({toString a}, {toString b})"
  | ~q(Nat), ~q(Multiset.sizeOf ($j : JumpSet)) => return s!"size({toString j})"
  | _, e => return toString e

partial def Expr.exportTheorem : Q(Prop) → TacticM (Array String)
  | ~q($P ∧ $Q) => return (← exportTheorem P) ++ (← exportTheorem Q)
  | ~q($P ∨ $Q) => return #[s!"or({← exportTheorem P}, {← exportTheorem Q})"]
  | ~q(¬$P) => return #[s!"not({← exportTheorem P})"]
  | ~q(∃ (a : $α), $P a) =>
      withLocalDeclQ `a .default α fun var ↦ do
      return #[s!"exists({`a.toString}, {← exportTheorem q($P $var)}"]
  | .forallE name domain body bi =>
    withLocalDecl name bi domain fun var ↦ do
      return #[s!"forall({name.toString}, {← exportTheorem (body.instantiate1 var)}"]
  | ~q((($P) : Prop) → $Q) => return #[s!"implies({← exportTheorem P}, {← exportTheorem Q})"]
  | ~q(@LT.lt ($α : Type) (_ : LT $α) $a $b) => return #[s!"lt({← Expr.exportTerm a}, {← Expr.exportTerm b})"]
  | ~q(@LE.le ($α : Type) (_ : LE $α) $a $b) => return #[s!"le({← Expr.exportTerm a}, {← Expr.exportTerm b})"]
  | _ => panic! "Expected a proposition as argument to `exportTheorem`."

elab "auto" fileName?:(str)? : tactic => withMainContext do
  let lctxTypes := (← getLCtx).decls.toArray.filterMap (·.map LocalDecl.type)
  let hypotheses : Array String ← lctxTypes.filter Expr.isProp |>.concatMapM Expr.exportTheorem
  let decls : Array String := lctxTypes.filter (!·.isProp) |>.map toString
  let mainGoal ← Expr.exportTheorem (← getMainTarget)
  let output : String := (hypotheses ++ #["\n---"] ++ decls ++ #["¬--"] ++ mainGoal)
    |>.map (String.push · '\n') |>.foldl (init := "") String.append
  logInfo output
  if let some fileName := fileName? then
    IO.FS.writeFile fileName.getString output

example (h : 3 = 3) : 1 = 1 := by
  auto
  -- auto "test_output.txt"
  rfl
