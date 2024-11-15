import MotivatedMoves.Mirek.SmtHammer.SmtExpr
import MotivatedMoves.Mirek.SmtHammer.SmtModel
import Qq

structure SmtType where
  argsTypes : List SmtExpr
  outType : SmtExpr
  extraCond : SmtExpr → List SmtExpr := fun _ => []

def SmtType.bool : SmtType := {
  argsTypes := []
  outType := .str "Bool"
}
instance : Inhabited SmtType where default := SmtType.bool

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

#check List.replicate

partial
def SmtRichExpr.fromLeanNat (e : Q(Nat)) : Lean.Meta.MetaM SmtRichExpr
:= match e with
| ~q($a + $b) => return (.apply "+" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q($a - $b) => return (.apply "nat-sub" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q($a * $b) => return (.apply "*" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q($a / $b) => return (.apply "div" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q($a % $b) => return (.apply "mod" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q($a ^ $b) => do
  match b.getNat? with
    | some 0 => return .const 1
    | some 1 => fromLeanNat a
    | some n => return (.apply "*" (List.replicate n (← fromLeanNat a)))
    | none => return .atomic e .nat
| e => match e.getNat? with
  | some n => return .const n
  | none => return .atomic e .nat

partial
def SmtModel.natValue (m : SmtModel) (e : Q(Int)) : Lean.Meta.MetaM Nat
:= match e with
| ~q($a + $b) => return (← m.natValue a) + (← m.natValue b)
| ~q($a - $b) => return (← m.natValue a) - (← m.natValue b)
| ~q($a * $b) => return (← m.natValue a) * (← m.natValue b)
| ~q($a / $b) => return (← m.natValue a) / (← m.natValue b)
| ~q($a % $b) => return (← m.natValue a) % (← m.natValue b)
| ~q($a ^ $b) => do
  match b.getNat? with
    | some 0 => return 1
    | some 1 => m.natValue a
    | some n => return (← m.natValue a)^n
    | none => match m.intsD.get? e with
      | some n => return n.toNat
      | none => do
        let eStr ← Lean.Meta.ppExpr e
        throwError s!"natValue: Expression not covered by the model: {eStr}"
| e => match e.getNat? with
  | some n => return n
  | none => match m.intsD.get? e with
    | some n => return n.toNat
    | none => do
      let eStr ← Lean.Meta.ppExpr e
      throwError s!"natValue: Expression not covered by the model: {eStr}"

partial
def SmtRichExpr.fromLeanInt (e : Q(Int)) : Lean.Meta.MetaM SmtRichExpr
:= match e with
| ~q($a + $b) => return (.apply "+" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q($a - $b) => return (.apply "-" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q(- $a) => return (.apply "-" [(← fromLeanInt a)])
| ~q($a * $b) => return (.apply "*" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q($a / $b) => return (.apply "div" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q($a % $b) => return (.apply "mod" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q($a ^ $b) => do
  match b.getNat? with
    | some 0 => return .const 1
    | some 1 => fromLeanInt a
    | some n => return (.apply "*" (List.replicate n (← fromLeanInt a)))
    | none => return .atomic e .int
| ~q(↑($a : Nat)) => SmtRichExpr.fromLeanNat a
| e => match e.getNat? with
  | some n => return .const n
  | none => return .atomic e .nat

partial
def SmtModel.intValue (m : SmtModel) (e : Q(Int)) : Lean.Meta.MetaM Int
:= match e with
| ~q($a + $b) => return (← m.intValue a) + (← m.intValue b)
| ~q($a - $b) => return (← m.intValue a) - (← m.intValue b)
| ~q(- $a) => return -(← m.intValue a)
| ~q($a * $b) => return (← m.intValue a) * (← m.intValue b)
| ~q($a / $b) => return (← m.intValue a) / (← m.intValue b)
| ~q($a % $b) => return (← m.intValue a) % (← m.intValue b)
| ~q($a ^ $b) => do
  match b.getNat? with
    | some 0 => return 1
    | some 1 => m.intValue a
    | some n => return (← m.intValue a)^n
    | none => match m.intsD.get? e with
      | some n => return n
      | none => do
        let eStr ← Lean.Meta.ppExpr e
        throwError s!"intValue: Expression not covered by the model: {eStr}"
| ~q(↑($a : Nat)) => ↑(m.natValue a)
| e => match e.getNat? with
  | some n => return n
  | none => match m.intsD.get? e with
    | some n => return n
    | none => do
      let eStr ← Lean.Meta.ppExpr e
      throwError s!"Expression not covered by the model: {eStr}"

partial
def SmtRichExpr.fromLeanProp : Q(Prop) → Lean.Meta.MetaM SmtRichExpr
| (.mdata _ e) => fromLeanProp e
| ~q(True) => return .str "true"
| ~q(False) => return .str "false"
| ~q($a ∧ $b) => return (.apply "and" [(← fromLeanProp a), (← fromLeanProp b)])
| ~q($a ∨ $b) => return (.apply "or" [(← fromLeanProp a), (← fromLeanProp b)])
| ~q(¬ $a) => return (.apply "not" [(← fromLeanProp a)])
| ~q(($a : Int) = $b) => return (.apply "=" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q(($a : Nat) = $b) => return (.apply "=" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q(($a : Int) ≤ $b) => return (.apply "<=" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q(($a : Nat) ≤ $b) => return (.apply "<=" [(← fromLeanNat a), (← fromLeanNat b)])
| ~q(($a : Int) < $b) => return (.apply "<" [(← fromLeanInt a), (← fromLeanInt b)])
| ~q(($a : Nat) < $b) => return (.apply "<" [(← fromLeanNat a), (← fromLeanNat b)])
| e@(.forallE _ a b _) => do -- implication doesn't work with Qq
  let ta ← Lean.Meta.inferType a
  if ta.isProp then
    return (.apply "=>" [(← fromLeanProp a), (← fromLeanProp b)])
  else
    return .atomic e .bool
| e => return .atomic e .bool

partial
def SmtModel.propValue (m : SmtModel) : Q(Prop) → Lean.Meta.MetaM Bool
| (.mdata _ e) => m.propValue e
| ~q(True) => return true
| ~q(False) => return false
| ~q($a ∧ $b) => return (← m.propValue a) && (← m.propValue b)
| ~q($a ∨ $b) => return (← m.propValue a) || (← m.propValue b)
| ~q(¬ $a) => return !(← m.propValue a)
| ~q(($a : Int) = $b) => return (← m.intValue a) == (← m.intValue b)
| ~q(($a : Nat) = $b) => return (← m.natValue a) == (← m.natValue b)
| ~q(($a : Int) ≤ $b) => return (← m.intValue a) <= (← m.intValue b)
| ~q(($a : Nat) ≤ $b) => return (← m.natValue a) <= (← m.natValue b)
| ~q(($a : Int) < $b) => return (← m.intValue a) < (← m.intValue b)
| ~q(($a : Nat) < $b) => return (← m.natValue a) < (← m.natValue b)
| e@(.forallE _ a b _) => do -- implication doesn't work with Qq
  let ta ← Lean.Meta.inferType a
  if ta.isProp then
    return (!(← m.propValue a)) || (← m.propValue b)
  else
    match m.boolsD.get? e with
    | some b => return b
    | none => do
      let eStr ← Lean.Meta.ppExpr e
      throwError s!"propValue: Expression not covered by the model: {eStr}"
| e => match m.boolsD.get? e with
  | some b => return b
  | none => do
    let eStr ← Lean.Meta.ppExpr e
    throwError s!"propValue: Expression not covered by the model: {eStr}"

def SmtRichExpr.fromLeanProp? (e : Lean.Expr) : Lean.Meta.MetaM (Option SmtRichExpr)
:= do
  let e ← Lean.instantiateMVars e
  if ((← Lean.Meta.inferType e)) == q(Prop) then
    return some (← SmtRichExpr.fromLeanProp e)
  else
    return none

structure SmtNames where
  exprToName : Std.HashMap Lean.Expr String := .empty
  nameToExpr : Std.HashMap String Lean.Expr := .empty
  nameToType : Std.HashMap String SmtType := .empty
  nameList : Array String := .empty
  nextName : Nat := .zero
deriving Inhabited

abbrev SmtNamesM := StateM SmtNames

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

def SmtNamesM.exportTypes : SmtNamesM (Array SmtExpr)
:= do
  let state ← get
  let mut res : Array SmtExpr := #[]
  for name in state.nameList do
    let t := state.nameToType.get! name
    let v := (.str name)
    res := res.push (
      match t.argsTypes with
      | [] => .apply "declare-const"
          [v, t.outType]
      | l => .apply "declare-fun"
          [v, (.list l), t.outType]
    )
    for constraint in t.extraCond v do
      res := res.push (.assert constraint)
  return res

def SmtNamesM.runEmpty {α : Type} (cmd : SmtNamesM α) : α × SmtNames :=
  StateT.run cmd default
