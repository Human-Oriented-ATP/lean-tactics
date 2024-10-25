import MotivatedMoves.Mirek.SmtExpr
import Qq

structure SmtType where
  argsTypes : List SmtExpr
  outType : SmtExpr
  extraCond : SmtExpr → List SmtExpr := fun _ => []

def SmtType.bool : SmtType := {
  argsTypes := []
  outType := .str "Bool"
}
def SmtType.int : SmtType := {
  argsTypes := []
  outType := .str "Int"
}
def SmtType.nat : SmtType := {
  argsTypes := []
  outType := .str "Int"
  extraCond := fun v => [(SmtExpr.apply ">=" [v, .const 0])]
}

inductive SmtRichExpr : Type where
| str (s : String)
| const (n : Nat)
| list (l : List SmtRichExpr)
| atomic (e : Lean.Expr) (t : SmtType)
instance : Inhabited SmtRichExpr where default := .const 0

def SmtRichExpr.apply (op : String) (args : List SmtRichExpr) : SmtRichExpr
:= (.list ((.str op)::args))
def SmtRichExpr.assert (e : SmtRichExpr) : SmtRichExpr
:= .apply "assert" [e]


open Qq

def Lean.Expr.getNat? : Lean.Expr → Option Nat
| .lit (.natVal n) => n
| .app (.app (.app (Lean.Expr.const `OfNat.ofNat _) _) x) _
  => getNat? x
| _ => none

partial
def SmtRichExpr.fromLeanNat : Q(Nat) → Lean.Meta.MetaM SmtRichExpr
| ~q($a + $b) => return (.apply "+" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q($a - $b) => return (.apply "nat-sub" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q($a * $b) => return (.apply "*" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q($a / $b) => return (.apply "div" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q($a % $b) => return (.apply "mod" [(← fromLeanNat a), (← fromLeanNat b)])
| e => match e.getNat? with
  | some n => return .const n
  | none => return .atomic e .nat

partial
def SmtRichExpr.fromLeanInt : Q(Int) → Lean.Meta.MetaM SmtRichExpr
| ~q($a + $b) => return (.apply "+" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q($a - $b) => return (.apply "-" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q(- $a) => return (.apply "-" [(← fromLeanInt a)])
| ~q($a * $b) => return (.apply "*" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q($a / $b) => return (.apply "div" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q($a % $b) => return (.apply "mod" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q(↑($a : Nat)) => SmtRichExpr.fromLeanNat a
| e => return .atomic e .int

partial
def SmtRichExpr.fromLeanProp : Q(Prop) → Lean.Meta.MetaM SmtRichExpr
| ~q(true) => return .str "true"
| ~q(false) => return .str "false"
| ~q($a ∧ $b) => return (.apply "and" [(← fromLeanProp a), (← fromLeanProp b)])
| ~q($a ∨ $b) => return (.apply "or" [(← fromLeanProp a), (← fromLeanProp b)])
| ~q(¬ $a) => return (.list [(.str "not"), (← fromLeanProp a)])
| ~q(($a : Int) = $b) => return (.apply "=" [(← fromLeanInt a), (← fromLeanInt b)])
| e@(.forallE _ a b _) => do -- implication doesn't work with Qq
  let ta ← Lean.Meta.inferType a
  if ta.isProp then
    return (.apply "=>" [(← fromLeanProp a), (← fromLeanProp b)])
  else
    return .atomic e .bool
| e => return .atomic e .bool

structure SmtNames where
  exprToName : Std.HashMap Lean.Expr String := .empty
  nameToExpr : Std.HashMap String Lean.Expr := .empty
  nameToType : Std.HashMap String SmtType := .empty
  nameList : Array String := .empty
  nextName : Nat := .zero
deriving Inhabited

abbrev SmtNamesM := StateT SmtNames Lean.Elab.Tactic.TacticM

partial
def SmtNamesM.richToSmt : SmtRichExpr → SmtNamesM SmtExpr
| .str s => return (.str s)
| .const n => return (.const n)
| .list l => return (.list (← l.mapM richToSmt))
| .atomic e t => do
  let state ← get
  match state.exprToName.get? e with
  | .some name => return (.str name)
  | .none => do
    let name := s!"x{state.nextName}"
    set ({
      exprToName := state.exprToName.insert e name
      nameToExpr := state.nameToExpr.insert name e
      nameToType := state.nameToType.insert name t
      nameList := state.nameList.push name
      nextName := state.nextName+1
    } : SmtNames)
    return (.str name)
