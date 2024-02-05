import Mathlib.Geometry.Euclidean.Angle.Sphere
import MotivatedMoves.Mirek.GeoModel
import Qq

open Lean ProofWidgets
namespace GeoLogic

inductive Step
-- movable
| point (pos : Model.Point)
| pointL (pos : Float) (li : Nat)
| pointC (pos : Float) (ci : Nat)
| lineP (d : Float) (pi : Nat)
| paralineL (pos : Float) (li : Nat)
| paralinePP (pos : Float) (pi1 pi2 : Nat)
| perplineL (pos : Float) (li : Nat)
| perplinePP (pos : Float) (pi1 pi2 : Nat)
| circleP (r : Float) (pi : Nat)
| compassC (center : Model.Point) (ci : Nat)
| compassPP (center : Model.Point) (pi1 pi2 : Nat)
| circumcircleP (relcenter : Model.Vector) (pi : Nat)
| circumcirclePP (coef : Float) (pi1 pi2 : Nat)
-- fixed
| midpointPP (pi1 pi2 : Nat)
| intersectionLL (li1 li2 : Nat)
| intersectionLC0 (li1 ci2 : Nat)
| intersectionLC1 (li1 ci2 : Nat)
| intersectionLCr0 (li1 ci2 pi : Nat)
| intersectionLCr1 (li1 ci2 pi : Nat)
| intersectionCC0 (ci1 ci2 : Nat)
| intersectionCC1 (ci1 ci2 : Nat)
| intersectionCCr0 (ci1 ci2 pi : Nat)
| intersectionCCr1 (ci1 ci2 pi : Nat)
| footPL (pi li : Nat)
| footPPP (pi pi1 pi2 : Nat)
| footPC0 (pi ci : Nat)
| footPC1 (pi ci : Nat)
| centerC (ci : Nat)
| arcMidpointCPP (ci pi1 pi2 : Nat)
| linePP (pi1 pi2 : Nat)
| paralineLP (li pi : Nat)
| paralinePPP (pi1 pi2 pi3 : Nat)
| touchpointPC0 (pi ci : Nat)
| touchpointPC1 (pi ci : Nat)
| tangentAtPC (pi ci : Nat)
| perpBisPP (pi1 pi2 : Nat)
| perplineLP (li pi : Nat)
| perplinePPP (pi1 pi2 pi3 : Nat)
| angIBisPPP (pi pi1 pi2 : Nat)
| angOBisPPP (pi pi1 pi2 : Nat)
| circlePP (pi1 pi2 : Nat)
| compassCP (ci pi : Nat)
| compassPPP (pi1 pi2 pi : Nat)
| diaCirclePP (pi1 pi2 : Nat)
| circumcirclePPP (pi1 pi2 pi3 : Nat)

instance Step.ToJson : ToJson Step where
  toJson step := match step with
  | point pos => Json.arr #[toJson "point", toJson pos]
  | pointL pos li => Json.arr #[toJson "pointL", toJson pos, toJson li]
  | pointC pos ci => Json.arr #[toJson "pointC", toJson pos, toJson ci]
  | lineP d pi => Json.arr #[toJson "lineP", toJson d, toJson pi]
  | paralineL pos li => Json.arr #[toJson "paralineL", toJson pos, toJson li]
  | paralinePP pos pi1 pi2 => Json.arr #[toJson "paralinePP", toJson pos, toJson pi1, toJson pi2]
  | perplineL pos li => Json.arr #[toJson "perplineL", toJson pos, toJson li]
  | perplinePP pos pi1 pi2 => Json.arr #[toJson "perplinePP", toJson pos, toJson pi1, toJson pi2]
  | circleP r pi => Json.arr #[toJson "circleP", toJson r, toJson pi]
  | compassC center ci => Json.arr #[toJson "compassC", toJson center, toJson ci]
  | compassPP center pi1 pi2 => Json.arr #[toJson "compassPP", toJson center, toJson pi1, toJson pi2]
  | circumcircleP relcenter pi => Json.arr #[toJson "circumcircleP", toJson relcenter, toJson pi]
  | circumcirclePP coef pi1 pi2 => Json.arr #[toJson "circumcirclePP", toJson coef, toJson pi1, toJson pi2]
  | midpointPP pi1 pi2 => Json.arr #[toJson "midpointPP", toJson pi1, toJson pi2]
  | intersectionLL li1 li2 => Json.arr #[toJson "intersectionLL", toJson li1, toJson li2]
  | intersectionLC0 li1 ci2 => Json.arr #[toJson "intersectionLC0", toJson li1, toJson ci2]
  | intersectionLC1 li1 ci2 => Json.arr #[toJson "intersectionLC1", toJson li1, toJson ci2]
  | intersectionLCr0 li1 ci2 pi => Json.arr #[toJson "intersectionLCr0", toJson li1, toJson ci2, toJson pi]
  | intersectionLCr1 li1 ci2 pi => Json.arr #[toJson "intersectionLCr1", toJson li1, toJson ci2, toJson pi]
  | intersectionCC0 ci1 ci2 => Json.arr #[toJson "intersectionCC0", toJson ci1, toJson ci2]
  | intersectionCC1 ci1 ci2 => Json.arr #[toJson "intersectionCC1", toJson ci1, toJson ci2]
  | intersectionCCr0 ci1 ci2 pi => Json.arr #[toJson "intersectionCCr0", toJson ci1, toJson ci2, toJson pi]
  | intersectionCCr1 ci1 ci2 pi => Json.arr #[toJson "intersectionCCr1", toJson ci1, toJson ci2, toJson pi]
  | footPL pi li => Json.arr #[toJson "footPL", toJson pi, toJson li]
  | footPPP pi pi1 pi2 => Json.arr #[toJson "footPPP", toJson pi, toJson pi1, toJson pi2]
  | footPC0 pi ci => Json.arr #[toJson "footPC0", toJson pi, toJson ci]
  | footPC1 pi ci => Json.arr #[toJson "footPC1", toJson pi, toJson ci]
  | centerC ci => Json.arr #[toJson "centerC", toJson ci]
  | arcMidpointCPP ci pi1 pi2 => Json.arr #[toJson "arcMidpointCPP", toJson ci, toJson pi1, toJson pi2]
  | linePP pi1 pi2 => Json.arr #[toJson "linePP", toJson pi1, toJson pi2]
  | paralineLP li pi => Json.arr #[toJson "paralineLP", toJson li, toJson pi]
  | paralinePPP pi1 pi2 pi3 => Json.arr #[toJson "paralinePPP", toJson pi1, toJson pi2, toJson pi3]
  | touchpointPC0 pi ci => Json.arr #[toJson "touchpointPC0", toJson pi, toJson ci]
  | touchpointPC1 pi ci => Json.arr #[toJson "touchpointPC1", toJson pi, toJson ci]
  | tangentAtPC pi ci => Json.arr #[toJson "tangentAtPC", toJson pi, toJson ci]
  | perpBisPP pi1 pi2 => Json.arr #[toJson "perpBisPP", toJson pi1, toJson pi2]
  | perplineLP li pi => Json.arr #[toJson "perplineLP", toJson li, toJson pi]
  | perplinePPP pi1 pi2 pi3 => Json.arr #[toJson "perplinePPP", toJson pi1, toJson pi2, toJson pi3]
  | angIBisPPP pi pi1 pi2 => Json.arr #[toJson "angIBisPPP", toJson pi, toJson pi1, toJson pi2]
  | angOBisPPP pi pi1 pi2 => Json.arr #[toJson "angOBisPPP", toJson pi, toJson pi1, toJson pi2]
  | circlePP pi1 pi2 => Json.arr #[toJson "circlePP", toJson pi1, toJson pi2]
  | compassCP ci pi => Json.arr #[toJson "circlePP", toJson ci, toJson pi]
  | compassPPP pi1 pi2 pi => Json.arr #[toJson "circlePP", toJson pi1, toJson pi2, toJson pi]
  | diaCirclePP pi1 pi2 => Json.arr #[toJson "diaCirclePP", toJson pi1, toJson pi2]
  | circumcirclePPP pi1 pi2 pi3 => Json.arr #[toJson "circumcirclePPP", toJson pi1, toJson pi2, toJson pi3]

instance Step.FromJson : FromJson Step where
  fromJson? json := do
  let err := Except.error "Invalid Json ConstructionStep";
  match json with
  | Json.arr arr => match arr.get? 0 with
    | "point" =>
      let #[_, pos] := arr | err
      let Except.ok pos := fromJson? pos | err
      return point pos
    | "pointL" =>
      let #[_, pos, li] := arr | err
      let Except.ok pos := fromJson? pos | err
      let Except.ok li := fromJson? li | err
      return pointL pos li
    | "pointC" =>
      let #[_, pos, ci] := arr | err
      let Except.ok pos := fromJson? pos | err
      let Except.ok ci := fromJson? ci | err
      return pointC pos ci
    | "lineP" =>
      let #[_, d, pi] := arr | err
      let Except.ok d := fromJson? d | err
      let Except.ok pi := fromJson? pi | err
      return lineP d pi
    | "paralineL" =>
      let #[_, pos, li] := arr | err
      let Except.ok pos := fromJson? pos | err
      let Except.ok li := fromJson? li | err
      return paralineL pos li
    | "paralinePP" =>
      let #[_, pos, pi1, pi2] := arr | err
      let Except.ok pos := fromJson? pos | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return paralinePP pos pi1 pi2
    | "perplineL" =>
      let #[_, pos, li] := arr | err
      let Except.ok pos := fromJson? pos | err
      let Except.ok li := fromJson? li | err
      return perplineL pos li
    | "perplinePP" =>
      let #[_, pos, pi1, pi2] := arr | err
      let Except.ok pos := fromJson? pos | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return perplinePP pos pi1 pi2
    | "circleP" =>
      let #[_, r, pi] := arr | err
      let Except.ok r := fromJson? r | err
      let Except.ok pi := fromJson? pi | err
      return circleP r pi
    | "compassC" =>
      let #[_, center, ci] := arr | err
      let Except.ok center := fromJson? center | err
      let Except.ok ci := fromJson? ci | err
      return compassC center ci
    | "compassPP" =>
      let #[_, center, pi1, pi2] := arr | err
      let Except.ok center := fromJson? center | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return compassPP center pi1 pi2
    | "circumcircleP" =>
      let #[_, relcenter, pi] := arr | err
      let Except.ok relcenter := fromJson? relcenter | err
      let Except.ok pi := fromJson? pi | err
      return circumcircleP relcenter pi
    | "circumcirclePP" =>
      let #[_, coef, pi1, pi2] := arr | err
      let Except.ok coef := fromJson? coef | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return circumcirclePP coef pi1 pi2
    | "midpointPP" =>
      let #[_, pi1, pi2] := arr | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return midpointPP pi1 pi2
    | "intersectionLL" =>
      let #[_, li1, li2] := arr | err
      let Except.ok li1 := fromJson? li1 | err
      let Except.ok li2 := fromJson? li2 | err
      return intersectionLL li1 li2
    | "intersectionLC0" =>
      let #[_, li1, ci2] := arr | err
      let Except.ok li1 := fromJson? li1 | err
      let Except.ok ci2 := fromJson? ci2 | err
      return intersectionLC0 li1 ci2
    | "intersectionLC1" =>
      let #[_, li1, ci2] := arr | err
      let Except.ok li1 := fromJson? li1 | err
      let Except.ok ci2 := fromJson? ci2 | err
      return intersectionLC1 li1 ci2
    | "intersectionLCr0" =>
      let #[_, li1, ci2, pi] := arr | err
      let Except.ok li1 := fromJson? li1 | err
      let Except.ok ci2 := fromJson? ci2 | err
      let Except.ok pi := fromJson? pi | err
      return intersectionLCr0 li1 ci2 pi
    | "intersectionLCr1" =>
      let #[_, li1, ci2, pi] := arr | err
      let Except.ok li1 := fromJson? li1 | err
      let Except.ok ci2 := fromJson? ci2 | err
      let Except.ok pi := fromJson? pi | err
      return intersectionLCr1 li1 ci2 pi
    | "intersectionCC0" =>
      let #[_, ci1, ci2] := arr | err
      let Except.ok ci1 := fromJson? ci1 | err
      let Except.ok ci2 := fromJson? ci2 | err
      return intersectionCC0 ci1 ci2
    | "intersectionCC1" =>
      let #[_, ci1, ci2] := arr | err
      let Except.ok ci1 := fromJson? ci1 | err
      let Except.ok ci2 := fromJson? ci2 | err
      return intersectionCC1 ci1 ci2
    | "intersectionCCr0" =>
      let #[_, ci1, ci2, pi] := arr | err
      let Except.ok ci1 := fromJson? ci1 | err
      let Except.ok ci2 := fromJson? ci2 | err
      let Except.ok pi := fromJson? pi | err
      return intersectionCCr0 ci1 ci2 pi
    | "intersectionCCr1" =>
      let #[_, ci1, ci2, pi] := arr | err
      let Except.ok ci1 := fromJson? ci1 | err
      let Except.ok ci2 := fromJson? ci2 | err
      let Except.ok pi := fromJson? pi | err
      return intersectionCCr1 ci1 ci2 pi
    | "footPL" =>
      let #[_, pi, li] := arr | err
      let Except.ok pi := fromJson? pi | err
      let Except.ok li := fromJson? li | err
      return footPL pi li
    | "footPPP" =>
      let #[_, pi, pi1, pi2] := arr | err
      let Except.ok pi := fromJson? pi | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return footPPP pi pi1 pi2
    | "footPC0" =>
      let #[_, pi, ci] := arr | err
      let Except.ok pi := fromJson? pi | err
      let Except.ok ci := fromJson? ci | err
      return footPC0 pi ci
    | "footPC1" =>
      let #[_, pi, ci] := arr | err
      let Except.ok pi := fromJson? pi | err
      let Except.ok ci := fromJson? ci | err
      return footPC1 pi ci
    | "centerC" =>
      let #[_, ci] := arr | err
      let Except.ok ci := fromJson? ci | err
      return centerC ci
    | "arcMidpointCPP" =>
      let #[_, ci, pi1, pi2] := arr | err
      let Except.ok ci := fromJson? ci | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return arcMidpointCPP ci pi1 pi2
    | "linePP" =>
      let #[_, pi1, pi2] := arr | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return linePP pi1 pi2
    | "paralineLP" =>
      let #[_, li, pi] := arr | err
      let Except.ok li := fromJson? li | err
      let Except.ok pi := fromJson? pi | err
      return paralineLP li pi
    | "paralinePPP" =>
      let #[_, pi1, pi2, pi3] := arr | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      let Except.ok pi3 := fromJson? pi3 | err
      return paralinePPP pi1 pi2 pi3
    | "touchpointPC0" =>
      let #[_, pi, ci] := arr | err
      let Except.ok pi := fromJson? pi | err
      let Except.ok ci := fromJson? ci | err
      return touchpointPC0 pi ci
    | "touchpointPC1" =>
      let #[_, pi, ci] := arr | err
      let Except.ok pi := fromJson? pi | err
      let Except.ok ci := fromJson? ci | err
      return touchpointPC1 pi ci
    | "tangentAtPC" =>
      let #[_, pi, ci] := arr | err
      let Except.ok pi := fromJson? pi | err
      let Except.ok ci := fromJson? ci | err
      return tangentAtPC pi ci
    | "perpBisPP" =>
      let #[_, pi1, pi2] := arr | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return perpBisPP pi1 pi2
    | "perplineLP" =>
      let #[_, li, pi] := arr | err
      let Except.ok li := fromJson? li | err
      let Except.ok pi := fromJson? pi | err
      return perplineLP li pi
    | "perplinePPP" =>
      let #[_, pi1, pi2, pi3] := arr | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      let Except.ok pi3 := fromJson? pi3 | err
      return perplinePPP pi1 pi2 pi3
    | "angIBisPPP" =>
      let #[_, pi, pi1, pi2] := arr | err
      let Except.ok pi := fromJson? pi | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return angIBisPPP pi pi1 pi2
    | "angOBisPPP" =>
      let #[_, pi, pi1, pi2] := arr | err
      let Except.ok pi := fromJson? pi | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return angOBisPPP pi pi1 pi2
    | "circlePP" =>
      let #[_, pi1, pi2] := arr | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return circlePP pi1 pi2
    | "compassCP" =>
      let #[_, ci, pi] := arr | err
      let Except.ok ci := fromJson? ci | err
      let Except.ok pi := fromJson? pi | err
      return compassCP ci pi
    | "compassPPP" =>
      let #[_, pi1, pi2, pi] := arr | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      let Except.ok pi := fromJson? pi | err
      return compassPPP pi1 pi2 pi
    | "diaCirclePP" =>
      let #[_, pi1, pi2] := arr | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      return diaCirclePP pi1 pi2
    | "circumcirclePPP" =>
      let #[_, pi1, pi2, pi3] := arr | err
      let Except.ok pi1 := fromJson? pi1 | err
      let Except.ok pi2 := fromJson? pi2 | err
      let Except.ok pi3 := fromJson? pi3 | err
      return circumcirclePPP pi1 pi2 pi3
    | _ => err
  | _ => err

open Model in def Step.apply? (step : Step) (model : Model) : Option Model :=
  match step with
  | point pos => some { model with points := model.points.push pos }
  | pointL pos li => do
    let some l := model.lines[li]? | none
    let p := l.v*pos + l.n*l.c
    some { model with points := model.points.push p }
  | pointC pos ci => do
    let some c := model.circles[ci]? | none
    let p : Point := c.c + (Vector.unit pos)*c.r
    return { model with points := model.points.push p }
  | lineP d pi => do
    let some p := model.points[pi]? | none
    let l := Line.PD p d
    return { model with lines := model.lines.push l }
  | paralineL pos li => do
    let some l := model.lines[li]? | none
    let l2 : Line := { n := l.n, c:=pos }
    return { model with lines := model.lines.push l2 }
  | paralinePP pos pi1 pi2 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let l2 : Line := { n := (Line.PP p1 p2).n, c := pos }
    return { model with lines := model.lines.push l2 }
  | perplineL pos li => do
    let some l := model.lines[li]? | none
    let l2 : Line := { n := l.v, c:=pos }
    return { model with lines := model.lines.push l2 }
  | perplinePP pos pi1 pi2 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let l2 : Line := { n := (Line.PP p1 p2).v, c := pos }
    return { model with lines := model.lines.push l2 }
  | circleP r pi => do
    let some p := model.points[pi]? | none
    let c : Circle := { c := p, r := r }
    return { model with circles := model.circles.push c }
  | compassC center ci => do
    let some c := model.circles[ci]? | none
    let c2 : Circle := { c := center, r := c.r }
    return { model with circles := model.circles.push c2 }
  | compassPP center pi1 pi2 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let c2 : Circle := { c := center, r := p1.dist p2 }
    return { model with circles := model.circles.push c2 }
  | circumcircleP relcenter pi => do
    let some p := model.points[pi]? | none
    let c : Circle := Circle.PP (p + relcenter) p
    return { model with circles := model.circles.push c }
  | circumcirclePP coef pi1 pi2 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let center : Point := centerFromCoef coef p1 p2
    let c := Circle.PP center p1
    return { model with circles := model.circles.push c }
  | midpointPP pi1 pi2 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let p := midpoint p1 p2
    return { model with points := model.points.push p }
  | intersectionLL li1 li2 => do
    let some l1 := model.lines[li1]? | none
    let some l2 := model.lines[li2]? | none
    let p := Model.intersectionLL l1 l2
    return { model with points := model.points.push p }
  | intersectionLC0 li1 ci2 => do
    let some l1 := model.lines[li1]? | none
    let some c2 := model.circles[ci2]? | none
    let p := firstP (intersectionLC l1 c2)
    return { model with points := model.points.push p }
  | intersectionLC1 li1 ci2 => do
    let some l1 := model.lines[li1]? | none
    let some c2 := model.circles[ci2]? | none
    let p := secondP (intersectionLC l1 c2)
    return { model with points := model.points.push p }
  | intersectionLCr0 li1 ci2 pi => do
    let some l1 := model.lines[li1]? | none
    let some c2 := model.circles[ci2]? | none
    let some ref := model.points[pi]? | none
    let p := closestP ref (intersectionLC l1 c2)
    return { model with points := model.points.push p }
  | intersectionLCr1 li1 ci2 pi => do
    let some l1 := model.lines[li1]? | none
    let some c2 := model.circles[ci2]? | none
    let some ref := model.points[pi]? | none
    let p := furthestP ref (intersectionLC l1 c2)
    return { model with points := model.points.push p }
  | intersectionCC0 ci1 ci2 => do
    let some c1 := model.circles[ci1]? | none
    let some c2 := model.circles[ci2]? | none
    let p := firstP (intersectionCC c1 c2)
    return { model with points := model.points.push p }
  | intersectionCC1 ci1 ci2 => do
    let some c1 := model.circles[ci1]? | none
    let some c2 := model.circles[ci2]? | none
    let p := secondP (intersectionCC c1 c2)
    return { model with points := model.points.push p }
  | intersectionCCr0 ci1 ci2 pi => do
    let some c1 := model.circles[ci1]? | none
    let some c2 := model.circles[ci2]? | none
    let some ref := model.points[pi]? | none
    let p := closestP ref (intersectionCC c1 c2)
    return { model with points := model.points.push p }
  | intersectionCCr1 ci1 ci2 pi => do
    let some c1 := model.circles[ci1]? | none
    let some c2 := model.circles[ci2]? | none
    let some ref := model.points[pi]? | none
    let p := furthestP ref (intersectionCC c1 c2)
    return { model with points := model.points.push p }
  | footPL pi li => do
    let some p := model.points[pi]? | none
    let some l := model.lines[li]? | none
    let foot := l.foot p
    return { model with points := model.points.push foot }
  | footPPP pi pi1 pi2 => do
    let some p := model.points[pi]? | none
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let l := Line.PP p1 p2
    let foot := l.foot p
    return { model with points := model.points.push foot }
  | footPC0 pi ci => do
    let some p := model.points[pi]? | none
    let some c := model.circles[ci]? | none
    let foot := c.foot0 p
    return { model with points := model.points.push foot }
  | footPC1 pi ci => do
    let some p := model.points[pi]? | none
    let some c := model.circles[ci]? | none
    let foot := c.foot1 p
    return { model with points := model.points.push foot }
  | centerC ci => do
    let some c := model.circles[ci]? | none
    return { model with points := model.points.push c.c }
  | arcMidpointCPP ci pi1 pi2 => do
    let some c := model.circles[ci]? | none
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let m := arcCenter c p1 p2
    return { model with points := model.points.push m }
  | linePP pi1 pi2 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let l := Line.PP p1 p2
    return { model with lines := model.lines.push l }
  | paralineLP li pi => do
    let some l := model.lines[li]? | none
    let some p := model.points[pi]? | none
    let l2 := Line.PN p l.n
    return { model with lines := model.lines.push l2 }
  | paralinePPP pi1 pi2 pi => do
    let some pi1 := model.points[pi1]? | none
    let some pi2 := model.points[pi2]? | none
    let some p := model.points[pi]? | none
    let l := Line.PP pi1 pi2
    let l2 := Line.PN p l.n
    return { model with lines := model.lines.push l2 }
  | touchpointPC0 pi ci => do
    let some p := model.points[pi]? | none
    let some c := model.circles[ci]? | none
    let p2 := firstP (touchpoints p c)
    return { model with points := model.points.push p2 }
  | touchpointPC1 pi ci => do
    let some p := model.points[pi]? | none
    let some c := model.circles[ci]? | none
    let p2 := secondP (touchpoints p c)
    return { model with points := model.points.push p2 }
  | tangentAtPC pi ci => do
    let some p := model.points[pi]? | none
    let some c := model.circles[ci]? | none
    let l := Model.tangentAtPC p c
    return { model with lines := model.lines.push l }
  | perpBisPP pi1 pi2 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let l := Model.perpBis p1 p2
    return { model with lines := model.lines.push l }
  | perplineLP li pi => do
    let some l := model.lines[li]? | none
    let some p := model.points[pi]? | none
    let l2 := Line.PN p l.v
    return { model with lines := model.lines.push l2 }
  | perplinePPP pi1 pi2 pi => do
    let some pi1 := model.points[pi1]? | none
    let some pi2 := model.points[pi2]? | none
    let some p := model.points[pi]? | none
    let l := Line.PP pi1 pi2
    let l2 := Line.PN p l.v
    return { model with lines := model.lines.push l2 }
  | angIBisPPP pi pi1 pi2 => do
    let some p := model.points[pi]? | none
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let l := angIBis p p1 p2
    return { model with lines := model.lines.push l }
  | angOBisPPP pi pi1 pi2 => do
    let some p := model.points[pi]? | none
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let l := angOBis p p1 p2
    return { model with lines := model.lines.push l }
  | circlePP pi1 pi2 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let c := Circle.PP p1 p2
    return { model with circles := model.circles.push c }
  | compassCP ci pi => do
    let some c := model.circles[ci]? | none
    let some p := model.points[pi]? | none
    let c2 : Circle := { c := p, r := c.r }
    return { model with circles := model.circles.push c2 }
  | compassPPP pi1 pi2 pi => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let some p := model.points[pi]? | none
    let c2 : Circle := { c := p, r := p1.dist p2 }
    return { model with circles := model.circles.push c2 }
  | diaCirclePP pi1 pi2 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let c := diaCircle p1 p2
    return { model with circles := model.circles.push c }
  | circumcirclePPP pi1 pi2 pi3 => do
    let some p1 := model.points[pi1]? | none
    let some p2 := model.points[pi2]? | none
    let some p3 := model.points[pi3]? | none
    let c := circumcircle p1 p2 p3
    return { model with circles := model.circles.push c }

def runSteps? (steps : List Step) : Option Model :=
  steps.foldlM
    (λ model step ↦ step.apply? model)
    { points := #[], lines := #[], circles := #[] }

initialize testRef : IO.Ref (List Step) ← IO.mkRef []

open Server RequestM in
@[server_rpc_method]
def runStepsRPC (steps : List Step) : RequestM (RequestTask Model) := do
  testRef.set steps
  match runSteps? steps with
  | some model => return (RequestTask.pure model)
  | none => throw (RequestError.invalidParams "Construction index (aux tail ctx) of bounds")

inductive LineDecc
| lineL (li : Nat)
| linePP (pi1 pi2 : Nat)
inductive AngleDesc
| angleLL (l1 l2 : LineDesc)
| arcCPP (ci pi1 pi2 : Nat)

structure GeoKnowledge where
  equalPoints : List (List Nat)
  equalLines : List (List Nat)
  equalCircles : List (List Nat)
  equalAngles : List (List AngleDesc)
  equalDist : List (List (Nat × Nat)) -- pairs of point indices
  rationalAngles : List (List Nat) -- line indices
  colinear : List (List Nat) -- point indices, at least 3
  concyclic : List (List Nat) -- point indices, at least 4

#check Module

def Point := ℝ × ℝ
deriving Dist, AddCommGroup, MetricSpace
instance : AddTorsor Point Point := by unfold Point; infer_instance
noncomputable instance : Module ℝ Point := by unfold Point; infer_instance

def Line := AffineSubspace ℝ Point
deriving Membership
def Circle := EuclideanGeometry.Sphere Point
deriving Membership

-- direction of a line is double since it is mod π
def Line.dir (l : Line) : Real.Angle := sorry
def dirPP (p1 p2 : Point) : Real.Angle := sorry

def isLinePP (l : Line) (p1 p2 : Point) : Prop :=
  p1 ∈ l ∧ p2 ∈ l ∧ p1 ≠ p2

theorem linePP_dir (l : Line) (p1 p2 : Point) :
  isLinePP l p1 p2 → l.dir + l.dir = dirPP p1 p2 := sorry

def paraLL (l1 l2 : Line) : Prop :=
  l1.dir = l2.dir
def paraLPP (l1 : Line) (p1 p2 : Point) : Prop :=
  ∃ l2 : Line, isLinePP l2 p1 p2 ∧ paraLL l1 l2
def perpLL (l1 l2 : Line) : Prop :=
  l1.dir + Real.pi = l2.dir
def perpLPP (l1 : Line) (p1 p2 : Point) : Prop :=
  ∃ l2 : Line, isLinePP l2 p1 p2 ∧ perpLL l1 l2
def collinear (p1 p2 p3 : Point) :=
  ∃ l : Line, p1 ∈ l ∧ p2 ∈ l ∧ p3 ∈ l

def isFreeCircum (c : Circle) (p1 p2 : Point) : Prop :=
  p1 ∈ c ∧ p2 ∈ c ∧ p1 ≠ p2
def isIntersectionLL (p : Point) (l1 l2 : Line) : Prop :=
  p ∈ l1 ∧ p ∈ l2 ∧ l1 ≠ l2
def isIntersectionLC (p : Point) (l1 : Line) (c2 : Circle) : Prop :=
  p ∈ l1 ∧ p ∈ c2
def isIntersectionCC (p : Point) (c1 c2 : Circle) : Prop :=
  p ∈ c1 ∧ p ∈ c2
def isMidpoint (mid p1 p2 : Point) : Prop := sorry
def isFootPL (foot p : Point) (l : Line) : Prop := sorry
def isFootPPP (foot p p1 p2 : Point) : Prop := sorry
def isFootPC0 (foot p : Point) (c : Circle) : Prop := sorry -- closer to p
def isFootPC1 (foot p : Point) (c : Circle) : Prop := sorry
def isArcMidpoint (mid : Point) (c : Circle) (p1 p2 : Point) : Prop := sorry -- p1 p2 ∈ c, direction depends on the order of p1 p2
def isParalinePL (pl : Line) (l : Line) (p : Point) : Prop :=
  paraLL pl l ∧ p ∈ l
def isParalinePPP (pl : Line) (p1 p2 p : Point) : Prop :=
  paraLPP pl p1 p2 ∧ p ∈ pl
def isTouchpoint (touch : Point) (p : Point) (c : Circle) : Prop := sorry -- line p t touches c
def isTangentAt (l : Line) (p : Point) (c : Circle) : Prop := sorry -- p ∈ c
def isPerpBis (l : Line) (p1 p2 : Point) : Prop := sorry
def isPerplinePL (pl : Line) (l : Line) (p : Point) : Prop :=
  perpLL pl l ∧ p ∈ l
def isPerplinePPP (pl : Line) (p1 p2 p : Point) : Prop :=
  perpLPP pl p1 p2 ∧ p ∈ pl
def isAngIBis (l : Line) (p p1 p2 : Point) : Prop := sorry -- p is the main vertex of the angle
def isAngOBis (l : Line) (p p1 p2 : Point) : Prop := sorry -- outer angle bisector
def isCirclePP (c : Circle) (center p : Point) : Prop :=
  c.center = center ∧ p ∈ c
def isCompassCP (res c : Circle) (p : Point) : Prop :=
  res.radius = c.radius ∧ res.center = p
def isCompassPPP (res : Circle) (p1 p2 p : Point) : Prop :=
  res.radius = Dist.dist p1 p2 ∧ res.center = p
def isDiacircle (c : Circle) (p1 p2 : Point) : Prop :=
  collinear p1 p2 c.center ∧ p1 ∈ c ∧ p2 ∈ c ∧ p1 ≠ p2
def isCircumcircle (c : Circle) (p1 p2 p3 : Point) : Prop :=
  p1 ∈ c ∧ p2 ∈ c ∧ p3 ∈ c ∧ p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3

-- instance Line.Membership : Membership Point Line where
--   mem (p : ℝ × ℝ) (l : AffineSubspace ℝ (ℝ × ℝ)) := p ∈ l
-- instance Circle.Membership : Membership Point Circle where
--   mem (p : ℝ × ℝ) (c : EuclideanGeometry.Sphere (ℝ × ℝ)) := p ∈ c

def linesPP (p1 p2 : Point) := { l : Line
| p1 ≠ p2 ∧ p1 ∈ l ∧ p2 ∈ l }
def intersectionsLL (l1 l2 : Line) := { p : Point
| l1 ≠ l2 ∧ p ∈ l1 ∧ p ∈ l2 }
def circumCirclesPPP (p1 p2 p3 : Point) := { c : Circle
| p1 ≠ p2 ∧ p2 ≠ p3 ∧ p3 ≠ p1 ∧ p1 ∈ c ∧ p2 ∈ c ∧ p3 ∈ c }

namespace stepsToTerm

structure Context where
  points : Array Nat
  lines : Array Nat
  circles : Array Nat
  depth : Nat

def Context.empty : Context := {
  points := #[]
  lines := #[]
  circles := #[]
  depth := 0
}

-- to avoid bugs mixing the different types
structure PointName where
  name : Name
structure LineName where
  name : Name
structure CircleName where
  name : Name

def Context.addPoint (ctx : Context) : Context × PointName :=
  let name := "p"++(toString ctx.points.size)
  ( { ctx with
      points := ctx.points.push ctx.depth,
      depth := ctx.depth+1 },
    { name := Name.mkSimple name }
  )
def Context.addLine (ctx : Context) : Context × LineName :=
  let name := "l"++(toString ctx.lines.size)
  ( { ctx with
      lines := ctx.lines.push ctx.depth,
      depth := ctx.depth+1 },
    { name := Name.mkSimple name }
  )
def Context.addCircle (ctx : Context) : Context × CircleName :=
  let name := "c"++(toString ctx.circles.size)
  ( { ctx with
      circles := ctx.circles.push ctx.depth,
      depth := ctx.depth+1 },
    { name := Name.mkSimple name }
  )
def Context.addCond (ctx : Context) : Context :=
  { ctx with depth := ctx.depth+1 }

open Qq

def Context.addPointC (ctx : Context) : (Context × PointName × Q(Point)) :=
  let (ctx, name) := ctx.addPoint
  (ctx.addCond, name, Expr.bvar 0)
def Context.addLineC (ctx : Context) : (Context × LineName × Q(Line)) :=
  let (ctx, name) := ctx.addLine
  (ctx.addCond, name, Expr.bvar 0)
def Context.addCircleC (ctx : Context) : (Context × CircleName × Q(Circle)) :=
  let (ctx, name) := ctx.addCircle
  (ctx.addCond, name, Expr.bvar 0)

def Context.point (ctx : Context) (i : Nat) : Q(Point) :=
  Expr.bvar (ctx.depth - ctx.points[i]!)
def Context.line (ctx : Context) (i : Nat) : Q(Line) :=
  Expr.bvar (ctx.depth - ctx.lines[i]!)
def Context.circle (ctx : Context) (i : Nat) : Q(Circle) :=
  Expr.bvar (ctx.depth - ctx.circles[i]!)

def outAddPoint (name : PointName) (body : Expr) : Expr :=
  Expr.forallE name.name (Expr.const ``Point []) body BinderInfo.default
def outAddLine (name : LineName) (body : Expr) : Expr :=
  Expr.forallE name.name (Expr.const ``Line []) body BinderInfo.default
def outAddCircle (name : CircleName) (body : Expr) : Expr :=
  Expr.forallE name.name (Expr.const ``Circle []) body BinderInfo.default
def outAddCond (cond : Expr) (body : Expr) : Expr :=
  Expr.forallE "_" cond body BinderInfo.default
def outAddPointC (name : PointName) (cond : Expr) (body : Expr) : Expr :=
  outAddPoint name <| outAddCond cond body
def outAddLineC (name : LineName) (cond : Expr) (body : Expr) : Expr :=
  outAddLine name <| outAddCond cond body
def outAddCircleC (name : CircleName) (cond : Expr) (body : Expr) : Expr :=
  outAddCircle name <| outAddCond cond body

def aux (steps : List Step) (ctx : Context) : Expr :=
  match steps with
  | [] => Expr.const ``True []
  | step::tail =>
    match step with
    | Step.point coor =>
      let (ctx,name) := ctx.addPoint
      outAddPoint name (aux tail ctx)
    | Step.pointL coor li =>
      let l := ctx.line li
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q($cur ∈ $l) (aux tail ctx)
    | Step.pointC pos ci =>
      let c := ctx.circle ci
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q($cur ∈ $c) (aux tail ctx)
    | Step.lineP d pi =>
      let p := ctx.point pi
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q($p ∈ $cur) (aux tail ctx)
    | Step.paralineL pos li =>
      let l := ctx.line li
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(paraLL $cur $l) (aux tail ctx)
    | Step.paralinePP pos pi1 pi2 =>
      let p1 := ctx.point pi1
      let (ctx,name,cur) := ctx.addLineC
      let p2 := ctx.point pi2
      outAddLineC name q(paraLPP $cur $p1 $p2) (aux tail ctx)
    | Step.perplineL pos li =>
      let l := ctx.line li
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(perpLL $cur $l) (aux tail ctx)
    | Step.perplinePP pos pi1 pi2 =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(perpLPP $cur $p1 $p2) (aux tail ctx)
    | Step.circleP r pi =>
      let p := ctx.point pi
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q(($cur).center = $p) (aux tail ctx)
    | Step.compassC center ci =>
      let c := ctx.circle ci
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q(($cur).radius = ($c).radius) (aux tail ctx)
    | Step.compassPP center pi1 pi2 =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q(($cur).radius = Dist.dist $p1 $p2) (aux tail ctx)
    | Step.circumcircleP relcenter pi =>
      let p := ctx.point pi
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q($p ∈ $cur) (aux tail ctx)
    | Step.circumcirclePP coef pi1 pi2 =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q(isFreeCircum $cur $p1 $p2) (aux tail ctx)
    | Step.midpointPP pi1 pi2 =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isMidpoint $cur $p1 $p2) (aux tail ctx)
    | Step.intersectionLL li1 li2 =>
      let l1 := ctx.line li1
      let l2 := ctx.line li2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isIntersectionLL $cur $l1 $l2) (aux tail ctx)
    | Step.intersectionLC0 li1 ci2 =>
      let l1 := ctx.line li1
      let c2 := ctx.circle ci2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isIntersectionLC $cur $l1 $c2) (aux tail ctx)
    | Step.intersectionLC1 li1 ci2 =>
      let l1 := ctx.line li1
      let c2 := ctx.circle ci2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isIntersectionLC $cur $l1 $c2) (aux tail ctx)
    | Step.intersectionLCr0 li1 ci2 pi =>
      let l1 := ctx.line li1
      let c2 := ctx.circle ci2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isIntersectionLC $cur $l1 $c2) (aux tail ctx)
    | Step.intersectionLCr1 li1 ci2 pi =>
      let l1 := ctx.line li1
      let c2 := ctx.circle ci2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isIntersectionLC $cur $l1 $c2) (aux tail ctx)
    | Step.intersectionCC0 ci1 ci2 =>
      let c1 := ctx.circle ci1
      let c2 := ctx.circle ci2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isIntersectionCC $cur $c1 $c2) (aux tail ctx)
    | Step.intersectionCC1 ci1 ci2 =>
      let c1 := ctx.circle ci1
      let c2 := ctx.circle ci2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isIntersectionCC $cur $c1 $c2) (aux tail ctx)
    | Step.intersectionCCr0 ci1 ci2 pi =>
      let c1 := ctx.circle ci1
      let c2 := ctx.circle ci2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isIntersectionCC $cur $c1 $c2) (aux tail ctx)
    | Step.intersectionCCr1 ci1 ci2 pi =>
      let c1 := ctx.circle ci1
      let c2 := ctx.circle ci2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isIntersectionCC $cur $c1 $c2) (aux tail ctx)
    | Step.footPL pi li =>
      let p := ctx.point pi
      let l := ctx.line li
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isFootPL $cur $p $l) (aux tail ctx)
    | Step.footPPP pi pi1 pi2 =>
      let p := ctx.point pi
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isFootPPP $cur $p $p1 $p2) (aux tail ctx)
    | Step.footPC0 pi ci =>
      let p := ctx.point pi
      let c := ctx.circle ci
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isFootPC0 $cur $p $c) (aux tail ctx)
    | Step.footPC1 pi ci =>
      let p := ctx.point pi
      let c := ctx.circle ci
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isFootPC1 $cur $p $c) (aux tail ctx)
    | Step.centerC ci =>
      let c := ctx.circle ci
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q($cur = ($c).center) (aux tail ctx)
    | Step.arcMidpointCPP ci pi1 pi2 =>
      let c := ctx.circle ci
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isArcMidpoint $cur $c $p1 $p2) (aux tail ctx)
    | Step.linePP pi1 pi2 =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(isLinePP $cur $p1 $p2) (aux tail ctx)
    | Step.paralineLP li pi =>
      let l := ctx.line li
      let p := ctx.point pi
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(isParalinePL $cur $l $p) (aux tail ctx)
    | Step.paralinePPP pi1 pi2 pi =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let p := ctx.point pi
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(isParalinePPP $cur $p1 $p2 $p) (aux tail ctx)
    | Step.touchpointPC0 pi ci =>
      let p := ctx.point pi
      let c := ctx.circle ci
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isTouchpoint $cur $p $c) (aux tail ctx)
    | Step.touchpointPC1 pi ci =>
      let p := ctx.point pi
      let c := ctx.circle ci
      let (ctx,name,cur) := ctx.addPointC
      outAddPointC name q(isTouchpoint $cur $p $c) (aux tail ctx)
    | Step.tangentAtPC pi ci =>
      let p := ctx.point pi
      let c := ctx.circle ci
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(isTangentAt $cur $p $c) (aux tail ctx)
    | Step.perpBisPP pi1 pi2 =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(isPerpBis $cur $p1 $p2) (aux tail ctx)
    | Step.perplineLP li pi =>
      let l := ctx.line li
      let p := ctx.point pi
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(isPerplinePL $cur $l $p) (aux tail ctx)
    | Step.perplinePPP pi1 pi2 pi =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let p := ctx.point pi
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(isPerplinePPP $cur $p1 $p2 $p) (aux tail ctx)
    | Step.angIBisPPP pi pi1 pi2 =>
      let p := ctx.point pi
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(isAngIBis $cur $p $p1 $p2) (aux tail ctx)
    | Step.angOBisPPP pi pi1 pi2 =>
      let p := ctx.point pi
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addLineC
      outAddLineC name q(isAngOBis $cur $p $p1 $p2) (aux tail ctx)
    | Step.circlePP pi1 pi2 =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q(isCirclePP $cur $p1 $p2) (aux tail ctx)
    | Step.compassCP ci pi =>
      let c := ctx.circle ci
      let p := ctx.point pi
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q(isCompassCP $cur $c $p) (aux tail ctx)
    | Step.compassPPP pi1 pi2 pi =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let p := ctx.point pi
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q(isCompassPPP $cur $p1 $p2 $p) (aux tail ctx)
    | Step.diaCirclePP pi1 pi2 =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q(isDiacircle $cur $p1 $p2) (aux tail ctx)
    | Step.circumcirclePPP pi1 pi2 pi3 =>
      let p1 := ctx.point pi1
      let p2 := ctx.point pi2
      let p3 := ctx.point pi3
      let (ctx,name,cur) := ctx.addCircleC
      outAddCircleC name q(isCircumcircle $cur $p1 $p2 $p3) (aux tail ctx)

end stepsToTerm

end GeoLogic
