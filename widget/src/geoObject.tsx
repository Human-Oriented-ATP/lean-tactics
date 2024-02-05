export type Point = [number,number]
export type Vector = [number,number]

export const epsilon = 1e-6

export interface Line {
  n : Vector
  c : number
}
export interface Circle {
  c : Point
  r : number
}
export interface Segment {
  start : Point
  end : Point
}
export interface ArcSegment {
  circle : Circle
  start : number
  end : number
}

export const zeroVec : Vector = [0,0]
export function mulVec(v:Vector, a:number) : Vector {
  const [x,y] = v
  return [a*x,a*y]
}
export function opVec(v:Vector) : Vector {
  const [x,y] = v
  return [-x,-y]
}
export function addVec(v1:Vector, v2:Vector) : Vector {
  const [x1,y1] = v1
  const [x2,y2] = v2
  return [x1+x2, y1+y2]
}
export function subVec(v1:Vector, v2:Vector) : Vector {
  const [x1,y1] = v1
  const [x2,y2] = v2
  return [x1-x2, y1-y2]
}
export function dotVV(v1:Vector, v2:Vector) : number {
  const [x1,y1] = v1
  const [x2,y2] = v2
  return x1*x2 + y1*y2
}
export function normVec(v:Vector) : number {
  return Math.sqrt(dotVV(v,v))
}
export function normalizeVec(v:Vector) : Vector {
  return mulVec(v, 1/normVec(v))
}
export function rot90cw(v:Vector) : Vector {
  const [x,y] = v
  return [y,-x]
}
export function rot90ccw(v:Vector) : Vector {
  const [x,y] = v
  return [-y,x]
}

export function directionV(v:Vector) : number {
  const [x,y] = v
  return Math.atan2(y,x) / Math.PI
}
export function directionPP(p1:Point, p2:Point) {
  return directionV(vectorPP(p1,p2))
}
export function unitVec(d:number) : Vector {
  const rd = d*Math.PI
  return [Math.cos(rd), Math.sin(rd)]
}

export function distPP(p1:Point, p2:Point) : number {
  return normVec(vectorPP(p1,p2))
}
export function distPL(p:Point, l:Line) : number {
  return Math.abs(dotVV(p,l.n)-l.c)
}
export function distPC(p:Point, c:Circle) : number {
  return Math.abs(distPP(p,c.c) - c.r)
}

export function vectorPP(p1:Point, p2:Point) : Vector {
  return subVec(p2,p1)
}
export function shiftPV(p:Point, v:Vector) : Point {
  return addVec(p,v)
}
export function midpoint(p1:Point, p2:Point) : Point {
  return mulVec(addVec(p1,p2), 0.5)
}

export function segment(start : Point, end : Point) : Segment { return {start : start, end : end} }
export function arcSegmentCDD(circle : Circle, start : number, end : number) : ArcSegment {
  return {circle : circle, start : start, end : end}
}
export function arcSegmentCPP(c : Circle, p1 : Point, p2 : Point) : ArcSegment {
  return {circle : c, start : directionV(vectorPP(c.c, p1)), end : directionV(vectorPP(c.c, p2))}
}
export function centerArc(arc : ArcSegment) : Point {
  var d1 = arc.start % 2
  var d2 = arc.end % 2
  if (d1 < 0) d1 += 2
  if (d2 < 0) d2 += 2
  if (d2 < d1) d2 += 2
  return shiftPV(
    arc.circle.c,
    mulVec(unitVec((d1+d2)/2), arc.circle.r)
  )
}

export function linePN(p:Point,n:Vector) : Line {
  n = normalizeVec(n)
  return {n:n, c:dotVV(n,p)}
}
export function linePV(p:Point,v:Vector) : Line {
  return linePN(p,rot90ccw(v))
}
export function linePP(p1 : Point, p2 : Point) : Line {
  return linePV(p1, vectorPP(p1,p2))
}
export function linePD(p : Point, d : number) : Line {
  return linePV(p, unitVec(d))
}
export function vectorL(l : Line) : Vector {
  return rot90cw(l.n)
}
export function directionL(l : Line) {
  return directionV(vectorL(l))
}
// in pixel coordinates, finds a segment to draw
export function cropLine(l : Line, left : number, up : number, right : number, down : number) : Segment | null {
  var res : (Point | null)[] = [null,null]
  var boundaries
  if (l.n[0] * l.n[1] < 0) boundaries = [[left,right],[up,down]]
  else boundaries = [[left,right],[down,up]]
  for (var coor=0; coor<2; coor++) {
    if (Math.abs(l.n[1-coor]) < epsilon) continue
    for (var bi=0; bi<2; bi++) {
      const bound = boundaries[coor][bi]
      var p : Point = [0,0]
      p[coor] = bound
      p[1-coor] = (l.c - bound*l.n[coor]) / l.n[1-coor]
      if ((p[1-coor] - boundaries[1-coor][0]) * (p[1-coor] - boundaries[1-coor][1]) <= 0)
        res[bi] = p
    }
  }
  if (res[0] === null || res[1] === null) return null
  else return { start : res[0], end : res[1] }
}

export function perpBis(p1 : Point, p2 : Point) {
  return linePN(midpoint(p1,p2), vectorPP(p1,p2))
}
export function angIBis(A : Point, B : Point, C : Point) {
  const v1 = normalizeVec(vectorPP(A,B))
  const v2 = normalizeVec(vectorPP(A,C))
  const cand1 = addVec(v1,v2)
  const cand2 = rot90cw(vectorPP(v1,v2))
  if (normVec(cand1) >= normVec(cand2)) return linePV(A, cand1)
  else return linePV(A, cand2)
}
export function angOBis(A : Point, B : Point, C : Point) {
  const v1 = normalizeVec(vectorPP(A,B))
  const v2 = normalizeVec(vectorPP(A,C))
  const cand1 = rot90cw(addVec(v1,v2))
  const cand2 = vectorPP(v1,v2)
  if (normVec(cand1) >= normVec(cand2)) return linePV(A, cand1)
  else return linePV(A, cand2)
}

export function circleCR(c : Point, r : number) : Circle {
  return {c:c, r:r}
}
export function circleCP(c : Point, x : Point) : Circle {
  return {c:c, r:distPP(c,x)}
}

export function footPL(p : Point, l : Line) : Point {
  const a = dotVV(p,l.n) - l.c
  return shiftPV(p, mulVec(l.n, -a))
}
export function footPC(p : Point, c : Circle) : Point {
  const v = normalizeVec(vectorPP(c.c,p))
  return shiftPV(c.c, mulVec(v, c.r))
}
export function footOpPC(p : Point, c : Circle) : Point {
  const v = normalizeVec(vectorPP(c.c,p))
  return shiftPV(c.c, mulVec(v, -c.r))
}

export function intersectionLL(l1 : Line, l2 : Line) : Point {
  const [nx1,ny1] = l1.n
  const [nx2,ny2] = l2.n
  const det = nx1*ny2 - nx2*ny1
  const x = (l1.c*ny2 - l2.c*ny1) / det
  const y = (l2.c*nx1 - l1.c*nx2) / det
  return [x,y]
}
export function intersectionLC(l : Line, c : Circle) : Point[] {
  // shift circle to center
  const y = l.c - dotVV(l.n, c.c)
  const x2 = c.r**2 - y**2
  if (x2 < -epsilon) return []
  if (x2 <= epsilon) return [shiftPV(c.c, mulVec(l.n, y))]
  else {
    const ax = Math.sqrt(x2)
    return [ax,-ax].map(x =>
      shiftPV(c.c, addVec(mulVec(vectorL(l), x), mulVec(l.n, y)))
    )
  }
}
export function intersectionCC(c1 : Circle, c2 : Circle) : Point[] {
  const centerDiff = vectorPP(c1.c, c2.c)
  const centerDist2 = dotVV(centerDiff,centerDiff)
  if (Math.abs(centerDist2) < epsilon) return []
  const relCenter = (c1.r**2 - c2.r**2) / centerDist2
  const center = shiftPV(midpoint(c1.c, c2.c), mulVec(centerDiff, relCenter/2))

  const radSum = c1.r + c2.r
  const radDiff = c1.r - c2.r
  const det = (radSum**2 - centerDist2) * (centerDist2 - radDiff**2)
  if (det < -epsilon) return []
  if (det <= epsilon) return [center]
  const centerDev = 0.5*Math.sqrt(det) / centerDist2
  return [centerDev, -centerDev].map(cd =>
    shiftPV(center, mulVec(rot90ccw(centerDiff), cd))
  )
}
export function closestPP(ps:Point[], p:Point) : Point | undefined {
  if (ps.length == 0) return
  var res : Point = ps[0]
  var d : number = distPP(res,p)
  for (var i = 1; i < ps.length; i++) {
    const d2 = distPP(ps[i], p)
    if (d2 < d) {
      res = ps[i]
      d = d2
    }
  }
  return res
}
export function furthestPP(ps:Point[], p:Point) : Point | undefined {
  if (ps.length == 0) return
  var res : Point = ps[0]
  var d : number = distPP(res,p)
  for (var i = 1; i < ps.length; i++) {
    const d2 = distPP(ps[i], p)
    if (d2 > d) {
      res = ps[i]
      d = d2
    }
  }
  return res
}

export function circumcenter(p1:Point,p2:Point,p3:Point) : Point {
  return intersectionLL(perpBis(p1,p2), perpBis(p1,p3))
}
export function circumcircle(p1:Point,p2:Point,p3:Point) : Circle {
  return circleCP(circumcenter(p1,p2,p3), p1)
}

export function diaCircle(p1:Point, p2:Point) : Circle {
  return circleCP(midpoint(p1,p2), p1)
}
export function touchpointsPC(p:Point, c:Circle) : Point[] {
  return intersectionCC(diaCircle(p,c.c), c)
}
export function tangentAtPC(p:Point, c:Circle) : Line { // assumes p on c
  return linePN(p, vectorPP(c.c,p))
}

// as complex numbers:
// x |-> (bar? x)*mul + add
export interface SimMap {
  mul : Vector
  add : Vector
  flip : boolean
}

export function realCpx(x:number) : Vector {
  return [x,0]
}
export const unitCpx : Vector = [1,0]
export function mulCpx(a:Vector, b:Vector) : Vector {
  const [ax,ay] = a
  const [bx,by] = b
  return [ax*bx-ay*by, ax*by+ay*bx]
}
export function conjCpx(v:Vector) : Vector {
  const [x,y] = v
  return [x,-y]
}
export function invCpx(v:Vector) : Vector {
  return mulVec(conjCpx(v), 1/dotVV(v,v))
}
export function divCpx(a:Vector,b:Vector) : Vector {
  return mulCpx(a,invCpx(b))
}

export function simMapDist(m : SimMap, l : number) : number {
  return l * normVec(m.mul)
}
export function simMapD(m : SimMap, d : number) : number {
  if (m.flip) d = -d
  return d + directionV(m.mul)
}
export function simMapV(m : SimMap, v : Vector) : Point {
  if (m.flip) v = conjCpx(v)
  return mulCpx(v,m.mul)
}
export function simMapP(m : SimMap, p : Point) : Point {
  return addVec(simMapV(m,p), m.add)
}
export function simMapL(m : SimMap, l : Line) : Line {
  var n : Vector = l.n
  var c : number = l.c
  if (m.flip) n = conjCpx(n)
  n = mulCpx(n, m.mul)
  // normalize again
  const size = normVec(n)
  c = c*size
  n = mulVec(n, 1/size)
  c = c + dotVV(n,m.add)
  return {n:n, c:c}
}
export function simMapC(m : SimMap, c : Circle) : Circle {
  return {c:simMapP(m,c.c), r:simMapDist(m,c.r)}
}
export function simMapSeg(m : SimMap, seg : Segment) : Segment {
  return {
    start : simMapP(m, seg.start),
    end : simMapP(m, seg.end),
  }
}
export function simMapArc(m : SimMap, arc : ArcSegment) : ArcSegment {
  const circle = simMapC(m, arc.circle)
  const start = simMapD(m, arc.start)
  const end = simMapD(m, arc.end)
  if (m.flip) return { circle : circle, start : end, end : start }
  else return { circle : circle, start : start, end : end }
}

export function inverseSM(m : SimMap) : SimMap {
  var mul = invCpx(m.mul)
  var add = mulCpx(opVec(m.add),mul)
  if (m.flip) {
    mul = conjCpx(mul)
    add = conjCpx(add)
  }
  return {
    mul:mul,
    add:add,
    flip:m.flip
  }
}
// left to right (postfix) composition
export function composeSM(m1 : SimMap, m2 : SimMap) : SimMap {
  var mul1 = m1.mul
  var add1 = m1.add
  var flip1 = m1.flip
  if (m2.flip) {
    mul1 = conjCpx(mul1)
    add1 = conjCpx(add1)
    flip1 = !flip1
  }
  return {
    mul:mulCpx(mul1,m2.mul),
    add:addVec(mulCpx(add1,m2.mul), m2.add),
    flip:flip1
  }
}
export function simMapFrom1P(p1:Point, p2:Point, mul:Vector, flip:boolean) : SimMap {
  if (flip) p1 = conjCpx(p1)
  const add = subVec(p2, mulCpx(mul, p1))
  return { mul:mul, add:add, flip:flip }
}
export function simMapFromPV(p1:Point, v1:Vector, p2:Point, v2:Vector, flip:boolean) : SimMap {
  if (flip) v1 = conjCpx(v1)
  return simMapFrom1P(p1,p2,divCpx(v2,v1),flip)
}
export function simMapFrom2P(a1:Point, b1:Point, a2:Point, b2:Point, flip:boolean) : SimMap {
  return simMapFromPV(a1,vectorPP(a1,b1),a2,vectorPP(a1,b1),flip)
}

export function centerSM(m : SimMap) { // assumes flip = false
  return divCpx(m.add, subVec(unitCpx, m.mul))
}

export function reflectionL(l : Line) : SimMap {
  const v = vectorL(l)
  const p = footPL(zeroVec, l)
  return simMapFromPV(p,v,p,v,true)
}
export function reflectionP(p : Point) : SimMap {
  return simMapFrom1P(p,p,realCpx(-1),false)
}
export function rotation(p : Point, angle : number) : SimMap {
  return simMapFrom1P(p,p,unitVec(angle),false)
}
export function translation(p1 : Point, p2 : Point) : SimMap {
  return simMapFrom1P(p1,p2,unitCpx,false)
}
export function homothethyP(p : Point, coef : number) : SimMap {
  return simMapFrom1P(p,p,realCpx(coef),false)
}
export function homothethyCC(c1 : Circle, c2 : Circle) : SimMap {
  const p1 = shiftPV(c1.c, realCpx(c1.r))
  const p2 = shiftPV(c2.c, realCpx(c2.r))
  return simMapFrom2P(c1.c,p1, c2.c,p2, false)
}

export const unitSimMap : SimMap = {mul:unitCpx, add:zeroVec, flip:false}

// predicates

export function equalP(p1 : Point, p2 : Point) { return distPP(p1,p2) <= epsilon }
export function equalL(l1 : Line, l2 : Line) {
  if (equalP(l1.n, l2.n) && Math.abs(l1.c - l2.c) <= epsilon) return true
  if (equalP(l1.n, opVec(l2.n)) && Math.abs(l1.c + l2.c) <= epsilon) return true
  return false
}
export function equalC(c1 : Circle, c2 : Circle) {
  return equalP(c1.c, c2.c) && Math.abs(c1.r - c2.r) <= epsilon
}
export function equalSeg(seg1 : Segment, seg2 : Segment) {
  return equalP(seg1.start, seg2.start) && equalP(seg1.end, seg2.end)
}
export function containedPL(p : Point, l : Line) { return distPL(p,l) <= epsilon }
export function containedPC(p : Point, c : Circle) { return distPC(p,c) <= epsilon }

export function equalD180(d1:number, d2:number) {
  const diff = Math.abs((d1-d2)%1)
  return diff < epsilon || Math.abs(diff-1) < epsilon
}
export function equalD360(d1:number, d2:number) {
  const diff = Math.abs((d1-d2)%2)
  return diff < epsilon || Math.abs(diff-2) < epsilon
}

export function equalArc(arc1:ArcSegment, arc2:ArcSegment) {
  return (
    equalC(arc1.circle, arc2.circle) &&
    equalD360(arc1.start, arc2.start) &&
    equalD360(arc1.end, arc2.end)
  )
}

// validity

export function validP(p : Point) : boolean {
  const [x,y] = p
  return Number.isFinite(x) && Number.isFinite(y)
}
export function validL(l : Line) : boolean {
  const [nx,ny] = l.n
  return Number.isFinite(l.c) && Math.abs(nx**2 + ny**2 - 1) < epsilon
}
export function normalizeL(l : Line) : Line {
  const x = 1/normVec(l.n)
  return { n:mulVec(l.n,x), c:l.c*x }
}
export function validC(c : Circle) : boolean {
  return Number.isFinite(c.r) && c.r > epsilon && validP(c.c)
}
export function validSeg(seg : Segment) : boolean {
  return validP(seg.start) && validP(seg.end)
}
export function validArc(arc : ArcSegment) : boolean {
  return validC(arc.circle) && Number.isFinite(arc.start) && Number.isFinite(arc.start)
}
export const invalidPoint : Point = [NaN,NaN]
export const invalidLine : Line = { n:invalidPoint, c:NaN }
export const invalidCircle : Circle = { c:invalidPoint, r:NaN }

// Type unions

export type Drawable = Point | Line | Circle | Segment | ArcSegment
export interface ProcessCases<Result> {
  point (p : Point) : Result
  line (l : Line) : Result
  circle (c : Circle) : Result
  segment (p : Segment) : Result
  arcSegment (a : ArcSegment) : Result
}
export function drawableCases<Result>(obj : Point | Line | Circle | Segment | ArcSegment, process : ProcessCases<Result>) {
  if ('n' in obj) {
    if (process.line) return process.line(obj)
  }
  else if ('r' in obj) {
    if (process.circle) return process.circle(obj)
  }
  else if ('circle' in obj) {
    if (process.arcSegment) return process.arcSegment(obj)
  }
  else if ('start' in obj) {
    if (process.segment) return process.segment(obj)
  }
  else {
    if (process.point) return process.point(obj)
  }
}

export function drawableEqual(obj1:Drawable, obj2:Drawable) {
  if (obj1 === obj2) return true
  return drawableCases(obj1, {
    point:(p1:Point) => {
      if (0 in obj2) return equalP(p1,obj2)
      else return false
    },
    line:(l1:Line) => {
      if ('n' in obj2) return equalL(l1,obj2)
      else return false
    },
    circle:(c1:Circle) => {
      if ('r' in obj2) return equalC(c1,obj2)
      else return false
    },
    segment:(seg1:Segment) => {
      if ('end' in obj2 && !('circle' in obj2)) return equalSeg(seg1,obj2)
      else return false
    },
    arcSegment:(arc1:ArcSegment) => {
      if ('end' in obj2 && 'circle' in obj2) return equalArc(arc1,obj2)
      else return false
    },
  })
}