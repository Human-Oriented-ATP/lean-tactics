import Lean
namespace GeoLogic

open Lean

def Float.π : Float := Float.atan2 0 (-1)
def Float.NaN : Float := 0.0 / 0.0

namespace Model

def epsilon := 1e-5

def Vector := Float × Float
deriving ToJson, FromJson
def Point := Float × Float
deriving ToJson, FromJson

structure Line where
  n : Vector -- supposed to be normalized
  c : Float
deriving ToJson, FromJson
structure Circle where
  c : Point
  r : Float
deriving ToJson, FromJson

def Point.invalid : Point := (Float.NaN, Float.NaN)
def Vector.invalid : Vector := (Float.NaN, Float.NaN)
def Line.invalid : Line := { n := Vector.invalid, c := Float.NaN }
def Circle.invalid : Circle := { c := Point.invalid, r := Float.NaN }

def Vector.zero : Vector := (0, 0)

instance Vector.HAdd : HAdd Vector Vector Vector where
  hAdd v1 v2 := let (x1,y1) := v1; let (x2,y2) := v2; (x1+x2,y1+y2)
instance Vector.HSub : HSub Vector Vector Vector where
  hSub v1 v2 := let (x1,y1) := v1; let (x2,y2) := v2; (x1-x2,y1-y2)
instance Vector.HMul : HMul Vector Float Vector where
  hMul v α := let (x,y) := v; (α*x, α*y)
instance Vector.HDiv : HDiv Vector Float Vector where
  hDiv v α := let (x,y) := v; (x/α, y/α)
instance Vector.Neg : Neg Vector where
  neg v := let (x,y) := v; (-x,-y)

def Vector.dot (v1 : Vector) (v2 : Vector) : Float :=
  let (x1,y1) := v1; let (x2,y2) := v2; x1*x2 + y1*y2
def Vector.norm (v : Vector) : Float := (v.dot v).sqrt
def Vector.normalize (v : Vector) : Vector := v / v.norm
def Vector.rot90cw (v : Vector) : Vector :=
  let (x,y) := v; (y,-x)
def Vector.rot90ccw (v : Vector) : Vector :=
  let (x,y) := v; (-y,x)

def Vector.dir (v : Vector) : Float :=
  let (x,y) := v; (Float.atan2 y x) / Float.π
def Vector.unit (d : Float) : Vector :=
  let rd := d*Float.π; (Float.cos rd , Float.sin rd)

def Point.asVec (p : Point) : Vector := p
def Vector.asPoint (v : Vector) : Point := v

instance Point.HAdd : HAdd Point Vector Point where
  hAdd p v := let (x1,y1) := p; let (x2,y2) := v; (x1+x2,y1+y2)
instance Point.HSub : HSub Point Vector Point where
  hSub v1 v2 := let (x1,y1) := v1; let (x2,y2) := v2; (x1-x2,y1-y2)

def Point.vector (p1 p2 : Point) : Vector := p2.asVec - p1.asVec

def Point.dist (p1 : Point) (p2 : Point) : Float := (p1.vector p2).norm
def Line.dist (l : Line) (p : Point) := Float.abs (l.n.dot p) - l.c
def Circle.dist (c : Circle) (p : Point) := Float.abs (c.c.dist p) - c.r

def midpoint (p1 p2 : Point) : Point := Vector.asPoint ((p1.asVec + p2.asVec)/2.0)
def Line.PN (p : Point) (n : Vector) : Line := let n := n.normalize; { n:=n, c:=n.dot p }
def Line.PV (p : Point) (v : Vector) : Line := Line.PN p v.rot90ccw
def Line.PP (p1 p2 : Point) : Line := Line.PV p1 (p1.vector p2)
def Line.PD (p : Point) (d : Float) := Line.PV p (Vector.unit d)
def Line.v (l : Line) : Vector := l.n.rot90cw
def Line.dir (l : Line) : Float := l.v.dir
def perpBis (p1 p2 : Point) : Line :=
  Line.PN (midpoint p1 p2) (p1.vector p2)
def angIBis (A B C : Point) : Line :=
  let v1 := (A.vector B).normalize
  let v2 := (A.vector C).normalize
  let cand1 := v1+v2
  let cand2 := (v2-v1).rot90cw
  if cand1.norm >= cand2.norm then Line.PV A cand1 else Line.PV A cand2
def angOBis (A B C : Point) : Line :=
  let v1 := (A.vector B).normalize
  let v2 := (A.vector C).normalize
  let cand1 := (v1+v2).rot90cw
  let cand2 := v2-v1
  if cand1.norm >= cand2.norm then Line.PV A cand1 else Line.PV A cand2
def Circle.PP (center p : Point) : Circle := { c := center, r := center.dist p }
def Line.foot (l : Line) (p : Point) :=
  let a := l.n.dot p - l.c; p - l.n*a
def Circle.foot0 (c : Circle) (p : Point) : Point :=
  let v := (c.c.vector p).normalize; (c.c + v*c.r)
def Circle.foot1 (c : Circle) (p : Point) : Point :=
  let v := (c.c.vector p).normalize; (c.c - v*c.r)

def intersectionLL (l1 l2 : Line) : Point :=
  let (nx1,ny1) := l1.n
  let (nx2,ny2) := l2.n
  let det := nx1*ny2 - nx2*ny1
  let x := (l1.c*ny2 - l2.c*ny1) / det
  let y := (l2.c*nx1 - l1.c*nx2) / det
  (x,y)

def intersectionLC (l : Line) (c : Circle) : List Point :=
  let y := l.c - (l.n.dot c.c)
  let x2 := c.r^2 - y^2
  if x2 < -epsilon then []
  else if x2 <= epsilon then [c.c + l.n*y]
  else
    let ax := Float.sqrt x2
    [ax,-ax].map λx ↦ c.c + l.v*x + l.n*y

def intersectionCC (c1 c2 : Circle) : List Point :=
  let centerDiff := c1.c.vector c2.c
  let centerDist2 := centerDiff.dot centerDiff
  if Float.abs centerDist2 < epsilon then []
  else
    let relCenter := (c1.r^2 - c2.r^2) / centerDist2
    let center := (midpoint c1.c c2.c) + centerDiff * (relCenter/2)
    let radSum := c1.r + c2.r
    let radDiff := c1.r - c2.r
    let det := (radSum^2 - centerDist2) * (centerDist2 - radDiff^2)
    if det < -epsilon then []
    else if det <= epsilon then [center]
    else
      let centerDev := 0.5 * (det.sqrt) / centerDist2
      [centerDev, -centerDev].map λcd ↦ center + centerDiff.rot90ccw * cd

def firstP (ps : List Point) : Point := ps.headD Point.invalid
def secondP (ps : List Point) : Point :=
  match ps with
  | [] => Point.invalid
  | [p] => p
  | _::p2::_ => p2
def bestP (value : Point → Float) (ps : List Point) : Point :=
  match ps with
  | [] => Point.invalid
  | [p] => p
  | a::b::t =>
    if value a > value b then
      bestP value (a::t)
    else
      bestP value (b::t)
def closestP (ref : Point) : List Point → Point := bestP (λx ↦ -ref.dist x)
def furthestP (ref : Point) : List Point → Point := bestP ref.dist

def circumcenter (p1 p2 p3 : Point) : Point :=
  intersectionLL (perpBis p1 p2) (perpBis p1 p3)
def circumcircle (p1 p2 p3 : Point) : Circle :=
  Circle.PP (circumcenter p1 p2 p3) p1
def diaCircle (p1 p2 : Point) : Circle :=
  Circle.PP (midpoint p1 p2) p1
def touchpoints (p : Point) (c : Circle) : List Point :=
  intersectionCC (diaCircle p c.c) c
-- assuming p lies on c
def tangentAtPC (p : Point) (c : Circle) : Line :=
  Line.PN p (c.c.vector p)

def arcCenter (c : Circle) (p1 p2 : Point) : Point :=
  let d1 := (c.c.vector p1).dir
  let d2 := (c.c.vector p2).dir
  let d2 := if d2 < d1 then d2 + 2 else d2
  c.c + (Vector.unit ((d1+d2)/2)) * c.r

def centerFromCoef (coef : Float) (p1 p2 : Point) : Point :=
  let v := (p1.vector p2).rot90cw
  (midpoint p1 p2) + v*coef
def getCircleCoef (c : Circle) (p1 p2 : Point) : Float :=
  let v : Vector := (p1.vector p2).rot90cw
  (v.dot (p1.vector c.c)) / (v.dot v)

end Model

structure Model where
  points : Array Model.Point
  lines : Array Model.Line
  circles : Array Model.Circle
deriving ToJson, FromJson

end GeoLogic
