import Lean.Elab.Tactic
import ProofWidgets.Component.HtmlDisplay

import Std.Util.TermUnsafe

import MotivatedMoves.Mirek.InsertButton

open Lean ProofWidgets
open scoped ProofWidgets.Jsx

namespace Rubik

inductive Color : Type
| empty
| white
| blue
| red
| yellow
| green
| orange
deriving ToJson, FromJson, Inhabited, Repr, DecidableEq

instance Color.ToExpr : ToExpr Color where
  toExpr (c : Color) : Expr := (match c with
    | empty => Expr.const ``Color.empty []
    | white => Expr.const ``Color.white []
    | blue => Expr.const ``Color.blue []
    | red => Expr.const ``Color.red []
    | yellow => Expr.const ``Color.yellow []
    | green => Expr.const ``Color.green []
    | orange => Expr.const ``Color.orange []
  )
  toTypeExpr := Expr.const ``Color []

def Color.toBExpr (color : Color) : Expr × Expr :=
(
  (match color with
  | empty => Expr.bvar 6
  | white => Expr.bvar 5
  | blue => Expr.bvar 4
  | red => Expr.bvar 3
  | yellow => Expr.bvar 2
  | green => Expr.bvar 1
  | orange => Expr.bvar 0),
  Expr.const ``Color []
)
def Color.letClosureAux : (List (String × Name)) → Expr → Expr
| [] => (λ e ↦ e)
| (n,v)::tail => (λ e ↦
  let e := Color.letClosureAux tail e
  ( -- let $n : Color := $v in $e
    Expr.letE n (Expr.const ``Color []) (Expr.const v []) e false
  )
)
def Color.letClosure : Expr → Expr := Color.letClosureAux (
[ ("N", ``Color.empty),
  ("W", ``Color.white),
  ("B", ``Color.blue),
  ("R", ``Color.red),
  ("Y", ``Color.yellow),
  ("G", ``Color.green),
  ("O", ``Color.orange),
])

set_option synthInstance.maxSize 1000 in
def Face := Color × Color × Color ×
            Color × Color × Color ×
            Color × Color × Color
deriving Inhabited, ToExpr, DecidableEq

instance Face.ToJson : ToJson Face where
  toJson := λ (a,b,c,d,e,f,g,h,i) ↦ toJson [a,b,c,d,e,f,g,h,i]
instance Face.FromJson : FromJson Face where
  fromJson? json := match (fromJson? json : Except String (Array Color)) with
  | Except.ok #[a,b,c,d,e,f,g,h,i] => Except.ok (a,b,c,d,e,f,g,h,i)
  | _ => Except.error "Json doesn't correcpond to a Rubik's Face"

def tupleExpr : List (Expr × Expr) → (Expr × Expr)
| [] => (Expr.const ``Unit.unit [], Expr.const ``Unit [])
| [x] => x
| (a,ta)::tail =>
  let (b,tb) := tupleExpr tail
  (
    ( -- (a,b)
      Expr.app (Expr.app (Expr.app (Expr.app
      (Expr.const ``Prod.mk [Level.zero, Level.zero])
      ta
      )
      tb
      )
      a
      )
      b
    ),
    ( -- ta × tb
      Expr.app (Expr.app
      (Expr.const ``Prod [Level.zero, Level.zero])
      ta
      )
      tb
    )
  )
def Face.toBExpr : Face → (Expr × Expr)
| (a,b,c,d,e,f,g,h,i) =>
  (tupleExpr ([a,b,c,d,e,f,g,h,i].map Color.toBExpr))

def Face.constant (c : Color) : Face :=
  (c, c, c, c, c, c, c, c, c)

inductive Rot
| id
| cw
| inv
| ccw

def Rot.apply {T : Type} (rot : Rot) (a b c d : T) : (T × T × T × T)
:= match rot with
| Rot.id => (a,b,c,d)
| Rot.cw => (d,a,b,c)
| Rot.inv => (c,d,a,b)
| Rot.ccw => (b,c,d,a)

def Rot.inverse : Rot → Rot
| Rot.id => Rot.id
| Rot.cw => Rot.ccw
| Rot.inv => Rot.inv
| Rot.ccw => Rot.cw

#check @Rot.apply

def Rot.rotate (rot : Rot) (face : Face) : Face :=
match face with
| ( a, b, c,
    d, e, f,
    g, h, i ) =>
    let ((a,b), (c,f), (i,h), (g,d)) := Rot.apply rot (a,b) (c,f) (i,h) (g,d)
    ( a, b, c,
      d, e, f,
      g, h, i)

def Face.Row := Color × Color × Color

def Face.get_row1 : Face → Face.Row
| (a,b,c,_,_,_,_,_,_) => (a,b,c)
def Face.set_row1 (face : Face) : (row : Face.Row) → Face
| (a,b,c) => match face with | (_,_,_,d,e,f,g,h,i) => (a,b,c,d,e,f,g,h,i)

def Face.get_row1_conv (face : Face) (rot : Rot) :=
  (rot.rotate face).get_row1
def Face.set_row1_conv (face : Face) (row : Face.Row) (rot : Rot) :=
  rot.inverse.rotate ((rot.rotate face).set_row1 row)

def Rot.row_apply (rot : Rot)
  (f1 : Face) (c1 : Rot)
  (f2 : Face) (c2 : Rot)
  (f3 : Face) (c3 : Rot)
  (f4 : Face) (c4 : Rot)
  := match rot.apply
    (f1.get_row1_conv c1)
    (f2.get_row1_conv c2)
    (f3.get_row1_conv c3)
    (f4.get_row1_conv c4)
  with
  | (r1, r2, r3, r4) => (
      (f1.set_row1_conv r1 c1),
      (f2.set_row1_conv r2 c2),
      (f3.set_row1_conv r3 c3),
      (f4.set_row1_conv r4 c4)
  )

def Cube := Face × Face × Face × Face × Face × Face
deriving Inhabited, DecidableEq

instance Cube.ToJson : ToJson Cube where
  toJson := λ (f1,f2,f3,f4,f5,f6) ↦ toJson [f1,f2,f3,f4,f5,f6]
instance Cube.FromJson : FromJson Cube where
  fromJson? json := match (fromJson? json : Except String (Array Face)) with
  | Except.ok #[f1,f2,f3,f4,f5,f6] => Except.ok (f1,f2,f3,f4,f5,f6)
  | _ => Except.error "Json doesn't correspond to a Rubik's Cube"

def Cube.toBExpr : Cube → (Expr × Expr)
| (f1,f2,f3,f4,f5,f6) =>
  (tupleExpr ([f1,f2,f3,f4,f5,f6].map Face.toBExpr))

instance Cube.ToExpr : ToExpr Cube where
  toExpr (cube : Cube) : Expr :=
    let (body,_) := Cube.toBExpr cube
    Color.letClosure
      body
  toTypeExpr := (Expr.const ``Cube [])

/-
   f1
f2 f3 f4
   f5
   f6
-/

def Cube.ini : Cube := (
  Face.constant Color.orange,
  Face.constant Color.green,
  Face.constant Color.white,
  Face.constant Color.blue,
  Face.constant Color.red,
  Face.constant Color.yellow,
)

-- f1
def Rot.U (rot : Rot) : Cube → Cube
| (f1,f2,f3,f4,f5,f6) =>
  let f1 := rot.rotate f1
  let (f6,f4,f3,f2) := rot.row_apply
    f6 Rot.inv
    f4 Rot.id
    f3 Rot.id
    f2 Rot.id
  (f1,f2,f3,f4,f5,f6)

-- f2
def Rot.L (rot : Rot) : Cube → Cube
| (f1,f2,f3,f4,f5,f6) =>
  let f2 := rot.rotate f2
  let (f1,f3,f5,f6) := rot.row_apply
    f1 Rot.cw
    f3 Rot.cw
    f5 Rot.cw
    f6 Rot.cw
  (f1,f2,f3,f4,f5,f6)

-- f3
def Rot.F (rot : Rot) : Cube → Cube
| (f1,f2,f3,f4,f5,f6) =>
  let f3 := rot.rotate f3
  let (f1,f4,f5,f2) := rot.row_apply
    f1 Rot.inv
    f4 Rot.cw
    f5 Rot.id
    f2 Rot.ccw
  (f1,f2,f3,f4,f5,f6)

-- f4
def Rot.R (rot : Rot) : Cube → Cube
| (f1,f2,f3,f4,f5,f6) =>
  let f4 := rot.rotate f4
  let (f1,f6,f5,f3) := rot.row_apply
    f1 Rot.ccw
    f6 Rot.ccw
    f5 Rot.ccw
    f3 Rot.ccw
  (f1,f2,f3,f4,f5,f6)

-- f5
def Rot.D (rot : Rot) : Cube → Cube
| (f1,f2,f3,f4,f5,f6) =>
  let f5 := rot.rotate f5
  let (f3,f4,f6,f2) := rot.row_apply
    f3 Rot.inv
    f4 Rot.inv
    f6 Rot.id
    f2 Rot.inv
  (f1,f2,f3,f4,f5,f6)

-- f6
def Rot.B (rot : Rot) : Cube → Cube
| (f1,f2,f3,f4,f5,f6) =>
  let f6 := rot.rotate f6
  let (f5,f4,f1,f2) := rot.row_apply
    f5 Rot.inv
    f4 Rot.ccw
    f1 Rot.id
    f2 Rot.cw
  (f1,f2,f3,f4,f5,f6)

def Cube.U (cube : Cube) : Cube := Rot.cw.U cube
def Cube.U' (cube : Cube) : Cube := Rot.ccw.U cube
def Cube.L (cube : Cube) : Cube := Rot.cw.L cube
def Cube.L' (cube : Cube) : Cube := Rot.ccw.L cube
def Cube.F (cube : Cube) : Cube := Rot.cw.F cube
def Cube.F' (cube : Cube) : Cube := Rot.ccw.F cube
def Cube.R (cube : Cube) : Cube := Rot.cw.R cube
def Cube.R' (cube : Cube) : Cube := Rot.ccw.R cube
def Cube.D (cube : Cube) : Cube := Rot.cw.D cube
def Cube.D' (cube : Cube) : Cube := Rot.ccw.D cube
def Cube.B (cube : Cube) : Cube := Rot.cw.B cube
def Cube.B' (cube : Cube) : Cube := Rot.ccw.B cube

def Cube.detectMove (cube1 cube2 : Cube) : String :=
  if cube2 = cube1.U then "U"
  else if cube2 = cube1.U' then "U'"
  else if cube2 = cube1.L then "L"
  else if cube2 = cube1.L' then "L'"
  else if cube2 = cube1.F then "F"
  else if cube2 = cube1.F' then "F'"
  else if cube2 = cube1.R then "R"
  else if cube2 = cube1.R' then "R'"
  else if cube2 = cube1.D then "D"
  else if cube2 = cube1.D' then "D'"
  else if cube2 = cube1.B then "B"
  else if cube2 = cube1.B' then "B'"
  else ""

open Server RequestM in
@[server_rpc_method]
def detectMoveQuery (cubes : Array Cube) : RequestM (RequestTask String) := do
  match cubes with
  | #[cube1,cube2] => return (RequestTask.pure (cube1.detectMove cube2))
  | _ => throw (RequestError.invalidParams "Wrong number of input cubes")

inductive Cube.solvable : Cube → Prop
| triv {c1 c2 c3 c4 c5 c6 : Color} : Cube.solvable
    ((c1,c1,c1,c1,c1,c1,c1,c1,c1),
     (c2,c2,c2,c2,c2,c2,c2,c2,c2),
     (c3,c3,c3,c3,c3,c3,c3,c3,c3),
     (c4,c4,c4,c4,c4,c4,c4,c4,c4),
     (c5,c5,c5,c5,c5,c5,c5,c5,c5),
     (c6,c6,c6,c6,c6,c6,c6,c6,c6))
| U {cube : Cube} (H : cube.U.solvable) : cube.solvable
| U' {cube : Cube} (H : cube.U'.solvable) : cube.solvable
| L {cube : Cube} (H : cube.L.solvable) : cube.solvable
| L' {cube : Cube} (H : cube.L'.solvable) : cube.solvable
| F {cube : Cube} (H : cube.F.solvable) : cube.solvable
| F' {cube : Cube} (H : cube.F'.solvable) : cube.solvable
| R {cube : Cube} (H : cube.R.solvable) : cube.solvable
| R' {cube : Cube} (H : cube.R'.solvable) : cube.solvable
| D {cube : Cube} (H : cube.D.solvable) : cube.solvable
| D' {cube : Cube} (H : cube.D'.solvable) : cube.solvable
| B {cube : Cube} (H : cube.B.solvable) : cube.solvable
| B' {cube : Cube} (H : cube.B'.solvable) : cube.solvable

#eval Cube.ini

example : Cube.ini.U.U'.solvable := Cube.solvable.triv

structure RubiksProps where
  cube : Cube
  deriving ToJson, FromJson, Inhabited

-- def eg := #["L", "L", "D⁻¹", "U⁻¹", "L", "D", "D", "L", "U⁻¹", "R", "D", "F", "F", "D"]
def eg : Array String := #[]

open Lean.Elab.Tactic in
elab "rubik_simp" : tactic =>
  withMainContext do
    let goal ← Elab.Tactic.getMainGoal
    let target ← goal.getType
    match target with
    | (Expr.app (Expr.const ``Cube.solvable _) cube) =>
      let cube ← unsafe Meta.evalExpr Cube (Expr.const ``Cube []) cube
      let cube := toExpr cube
      let target2 := (Expr.app (Expr.const ``Cube.solvable []) cube)
      let goal2 ← Meta.mkFreshExprMVar target2
      goal.assign goal2
      replaceMainGoal [goal2.mvarId!]
    | _ => do
      Lean.Meta.throwTacticEx `rubikSimp goal m!"Target must be of form (Cube.solvable _), got ({target})"

@[widget_module]
def Rubiks : Component RubiksProps where
  javascript := include_str ".." / ".." / "build" / "js" / "rubiks2.js"

structure ExtPanelWidgetProps extends PanelWidgetProps where
  range : Lsp.Range
deriving Server.RpcEncodable

def button (cw : Bool) (color : String) (side : String) (range : Lsp.Range) : Html :=
  <InsertEditButton
    icon={if cw then "cw" else "ccw"}
    color={color}
    range={range}
    insertion={s!"apply Cube.solvable.{side}{if cw then "" else "'"}; rubik_simp; save"}
    onWhitespace={true}/>
def buttonRow (cw : Bool) (range : Lsp.Range) : Html :=
  <div>
  {button cw "orange"     "U" range}
  {button cw "green"      "L" range}
  {button cw "snow"       "F" range}
  {button cw "dodgerblue" "R" range}
  {button cw "red"        "D" range}
  {button cw "yellow"     "B" range}
  </div>
def buttonPanel (range : Lsp.Range) : Html :=
  <div align="center">
  {buttonRow true range}
  {buttonRow false range}
  </div>

open Server RequestM in
@[server_rpc_method]
def RubikWidget.rpc (props : ExtPanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    match props.goals[0]? with
    | none => return <div />
    | some igoal =>
      let ocube : Option Cube ← igoal.ctx.val.runMetaM {} do
        let target : Expr ← igoal.mvarId.getType
        match target with
        | (Expr.app (Expr.const ``Cube.solvable _) cube) =>
          let cube ← unsafe Meta.evalExpr Cube (Expr.const ``Cube []) cube
          return some cube
        | _ => return none
      match ocube with
      | none => return <div />
      | some cube => return <div>
        <Rubiks cube={cube} />
        {(buttonPanel props.range)}
      </div>

@[widget_module]
def RubikWidget : Component ExtPanelWidgetProps :=
  mk_rpc_widget% RubikWidget.rpc

open Lean Parser Elab Tactic

syntax (name:=withRubiks) "with_rubiks" tacticSeq : tactic

@[tactic withRubiks]
def withRubiksImpl:Tactic
| stx@`(tactic|with_rubiks $seq) => do
  let some ⟨stxStart, stxEnd⟩ := (←getFileMap).rangeOfStx? stx | return
  -- the leading and trailing whitespaces around the `motivated_proof` syntax node
  let some (.original leading _ trailing _) := stx.getHeadInfo? | panic! s!"Could not extract head information from {stx}."
  let extractIndentation (s : Substring) : Nat :=
    s.toString |>.split (· = '\n') |>.getLast! |>.length -- compute the indentation of the last line in the string
  let indent : Nat := match seq.raw with
  | Syntax.node _ ``tacticSeq
   #[Syntax.node _ ``tacticSeq1Indented
   #[Syntax.node _ `null #[Syntax.missing, Syntax.missing]]] =>
    stxStart.character+2
  | _ => extractIndentation trailing
  let pos : Lsp.Position := { line := stxEnd.line+1, character := indent }
  let range : Lsp.Range := ⟨stxEnd, pos⟩
  Widget.savePanelWidgetInfo (hash RubikWidget.javascript) (return json%{
    range : $(range)
  } ) stx
  evalTacticSeq seq
| _ => throwUnsupportedSyntax

def puzzle : Cube :=
  let W := Color.white;
  let B := Color.blue;
  let R := Color.red;
  let Y := Color.yellow;
  let G := Color.green;
  let O := Color.orange;
  ( ( Y,W,O,
      R,O,O,
      Y,O,B
    ),
    ( G,G,G,
      G,G,O,
      B,R,W
    ),
    ( O,W,W,
      Y,W,Y,
      R,B,B
    ),
    ( R,B,B,
      G,B,W,
      W,B,G
    ),
    ( G,R,O,
      Y,R,Y,
      Y,W,W
    ),
    ( R,B,O,
      O,Y,G,
      R,R,Y
    )
  )

def easy_puzzle : Cube :=
  let O := Color.orange
  let G := Color.green
  let W := Color.white
  let B := Color.blue
  let R := Color.red
  let Y := Color.yellow
  ( ( G,O,O,
      G,O,O,
      W,B,B
    ),
    ( Y,Y,O,
      R,G,O,
      R,G,G
    ),
    ( G,W,W,
      G,W,W,
      R,W,W
    ),
    ( R,W,W,
      R,B,O,
      R,B,O
    ),
    ( Y,G,G,
      R,R,R,
      B,B,B
    ),
    ( Y,Y,Y,
      Y,Y,Y,
      O,B,B
    )
  )

#check Html

#html <Rubiks cube={puzzle.F.U.U} />

-- Solve a Rubik's Cube, then uncomment the last line
example : puzzle.solvable := by
  with_rubiks
    apply Cube.solvable.F; rubik_simp; save
    apply Cube.solvable.F; rubik_simp; save
    apply Cube.solvable.F; rubik_simp; save
    apply Cube.solvable.U'; rubik_simp; save
    apply Cube.solvable.F; rubik_simp; save
    apply Cube.solvable.D'; rubik_simp; save
    apply Cube.solvable.R; rubik_simp; save
    apply Cube.solvable.F'; rubik_simp; save
    apply Cube.solvable.L'; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.D'; rubik_simp; save
    apply Cube.solvable.F'; rubik_simp; save
    apply Cube.solvable.F'; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.F'; rubik_simp; save
    apply Cube.solvable.B'; rubik_simp; save
    apply Cube.solvable.R; rubik_simp; save
    apply Cube.solvable.D'; rubik_simp; save
    apply Cube.solvable.B'; rubik_simp; save
    apply Cube.solvable.D; rubik_simp; save
    apply Cube.solvable.R'; rubik_simp; save
    apply Cube.solvable.D; rubik_simp; save
    apply Cube.solvable.U'; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.U; rubik_simp; save
    apply Cube.solvable.D'; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.L'; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.D; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.D'; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.L'; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.B'; rubik_simp; save
    apply Cube.solvable.L'; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.U'; rubik_simp; save
    apply Cube.solvable.L'; rubik_simp; save
    apply Cube.solvable.U; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.U; rubik_simp; save
    apply Cube.solvable.B'; rubik_simp; save
    apply Cube.solvable.U'; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.B'; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.B'; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.L'; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.L'; rubik_simp; save
    apply Cube.solvable.L'; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.F'; rubik_simp; save
    apply Cube.solvable.B; rubik_simp; save
    apply Cube.solvable.B'; rubik_simp; save
    apply Cube.solvable.L; rubik_simp; save
    apply Cube.solvable.B'; rubik_simp; save
    apply Cube.solvable.L'; rubik_simp; save
    apply Cube.solvable.B'; rubik_simp; save
    apply Cube.solvable.F; rubik_simp; save
    apply Cube.solvable.triv
