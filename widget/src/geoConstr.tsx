import * as G from './geoObject'

export interface GeoModel {
  points : G.Point[]
  lines : G.Line[]
  circles : G.Circle[]
}

export type MovableStepOri = (
  ['point',G.Point] |
  ['pointL',number,number] |
  ['pointC',number,number] |
  ['lineP',number,number] |
  ['paralineL',number,number] |
  ['paralinePP',number,number,number] |
  ['perplineL',number,number] |
  ['perplinePP',number,number,number] |
  ['circleP',number,number] |
  ['compassC',G.Point,number] |
  ['compassPP',G.Point,number,number] |
  ['circumcircleP',G.Point,number] |
  ['circumcirclePP',number,number,number]
)
export type SolidStepOri = (
  ['midpointPP',number,number] |
  ['intersectionLL',number,number] |
  ['intersectionLC0',number,number] |
  ['intersectionLC1',number,number] |
  ['intersectionLCr0',number,number,number] |
  ['intersectionLCr1',number,number,number] |
  ['intersectionCC0',number,number] |
  ['intersectionCC1',number,number] |
  ['intersectionCCr0',number,number,number] |
  ['intersectionCCr1',number,number,number] |
  ['footPL',number,number] |
  ['footPPP',number,number,number] |
  ['footPC0',number,number] |
  ['footPC1',number,number] |
  ['centerC',number] |
  ['arcMidpointCPP',number,number,number] |
  ['linePP',number,number] |
  ['paralineLP',number,number] |
  ['paralinePPP',number,number,number] |
  ['touchpointPC0',number,number] |
  ['touchpointPC1',number,number] |
  ['tangentAtPC',number,number] |
  ['perpBisPP', number,number] |
  ['perplineLP', number, number] |
  ['perplinePPP', number, number, number] |
  ['angIBisPPP',number,number,number] |
  ['angOBisPPP',number,number,number] |
  ['circlePP', number,number] |
  ['compassCP', number,number] |
  ['compassPPP', number,number,number] |
  ['diaCirclePP', number,number] |
  ['circumcirclePPP', number,number,number]
)

export type MovableStep = (
  ['point',G.Point] |
  ['pointL',number,number] |
  ['pointC',number,number] |
  ['lineP',number,number] |
  ['paralineL',number,number] |
  ['paralinePP',number,number,number] |
  ['perplineL',number,number] |
  ['perplinePP',number,number,number] |
  ['circleP',number,number] |
  ['compassC',G.Point,number] |
  ['compassPP',G.Point,number,number] |
  ['circumcircleP',G.Point,number] |
  ['circumcirclePP',number,number,number]
)
export type SolidStep = (
  ['midpointPP',number,number] |
  ['intersectionLL',number,number] |
  ['intersectionLC0',number,number] |
  ['intersectionLC1',number,number] |
  ['intersectionLCr0',number,number,number] |
  ['intersectionLCr1',number,number,number] |
  ['intersectionCC0',number,number] |
  ['intersectionCC1',number,number] |
  ['intersectionCCr0',number,number,number] |
  ['intersectionCCr1',number,number,number] |
  ['footPL',number,number] |
  ['footPPP',number,number,number] |
  ['footPC0',number,number] |
  ['footPC1',number,number] |
  ['centerC',number] |
  ['arcMidpointCPP',number,number,number] |
  ['linePP',number,number] |
  ['paralineLP',number,number] |
  ['paralinePPP',number,number,number] |
  ['touchpointPC0',number,number] |
  ['touchpointPC1',number,number] |
  ['tangentAtPC',number,number] |
  ['perpBisPP', number,number] |
  ['perplineLP', number, number] |
  ['perplinePPP', number, number, number] |
  ['angIBisPPP',number,number,number] |
  ['angOBisPPP',number,number,number] |
  ['circlePP', number,number] |
  ['compassCP', number,number] |
  ['compassPPP', number,number,number] |
  ['diaCirclePP', number,number] |
  ['circumcirclePPP', number,number,number]
)

export type GeoStep = SolidStep | MovableStep

export function getCircleCoef(circ : G.Circle, p1 : G.Point, p2 : G.Point) {
  const v = G.rot90cw(G.vectorPP(p1,p2))
  return G.dotVV(v, G.vectorPP(p1,circ.c)) / G.dotVV(v,v)
}
export function centerFromCoef(coef : number, p1 : G.Point, p2 : G.Point) {
  const v = G.rot90cw(G.vectorPP(p1,p2))
  const center = G.shiftPV(G.midpoint(p1,p2), G.mulVec(v,coef))
  return center
}

export function applyStep(step : GeoStep, points : G.Point[], lines:G.Line[], circles:G.Circle[]) {
  switch (step[0]) {
    case 'point': {
      const [_,res] = step
      points.push(res)
      break
    }
    case 'pointL': {
      const [_,pos,li] = step
      const l = lines[li]
      points.push(G.addVec(
        G.mulVec(G.vectorL(l),pos), G.mulVec(l.n,l.c)))
      break
    }
    case 'pointC': {
      const [_,pos,ci] = step
      const c = circles[ci]
      points.push(G.shiftPV(c.c, G.mulVec(G.unitVec(pos), c.r)))
      break
    }
    case 'lineP': {
      const [_,d,pi] = step
      lines.push(G.linePD(points[pi], d))
      break
    }
    case 'paralineL': {
      const [_,c,li] = step
      lines.push({ n:lines[li].n, c:c })
      break
    }
    case 'paralinePP': {
      const [_,c,pi1,pi2] = step
      const p1 = points[pi1]
      const p2 = points[pi2]
      lines.push({ n:G.linePP(p1,p2).n, c:c })
      break
    }
    case 'perplineL': {
      const [_,c,li] = step
      lines.push({ n:G.vectorL(lines[li]), c:c })
      break
    }
    case 'perplinePP': {
      const [_,c,pi1,pi2] = step
      const p1 = points[pi1]
      const p2 = points[pi2]
      lines.push({ n:G.vectorL(G.linePP(p1,p2)), c:c })
      break
    }
    case 'circleP': {
      const [_,r,pi] = step
      circles.push(G.circleCR(points[pi], r))
      break
    }
    case 'compassC': {
      const [_,center,ci] = step
      circles.push(G.circleCR(center, circles[ci].r))
      break
    }
    case 'compassPP': {
      const [_,center,pi1,pi2] = step
      circles.push(G.circleCR(center, G.distPP(points[pi1], points[pi2])))
      break
    }
    case 'circumcircleP': {
      const [_,relcenter,pi] = step
      const p = points[pi]
      circles.push(G.circleCP(G.shiftPV(p,relcenter), p))
      break
    }
    case 'circumcirclePP': {
      const [_,coef,pi1,pi2] = step
      const center = centerFromCoef(coef, points[pi1], points[pi2])
      circles.push(G.circleCP(center, points[pi1]))
      break
    }
    case 'midpointPP': {
      const [_,pi1,pi2] = step
      points.push(G.midpoint(points[pi1], points[pi2]))
      break
    }
    case 'intersectionLL': {
      const [_,li1,li2] = step
      points.push(G.intersectionLL(lines[li1], lines[li2]))
      break
    }
    case 'intersectionLC0': {
      const [_,li1,ci2] = step
      const res = G.intersectionLC(lines[li1], circles[ci2])
      if (res.length == 0) points.push(G.invalidPoint)
      else points.push(res[0])
      break
    }
    case 'intersectionLC1': {
      const [_,li1,ci2] = step
      const res = G.intersectionLC(lines[li1], circles[ci2])
      if (res.length == 0) points.push(G.invalidPoint)
      else if(res.length == 1) points.push(res[0])
      else points.push(res[1])
      break
    }
    case 'intersectionLCr0': {
      const [_,li1,ci2,ri] = step
      const res = G.closestPP(G.intersectionLC(lines[li1],circles[ci2]), points[ri])
      if (res === undefined) points.push(G.invalidPoint)
      else points.push(res)
      break
    }
    case 'intersectionLCr1': {
      const [_,li1,ci2,ri] = step
      const res = G.furthestPP(G.intersectionLC(lines[li1],circles[ci2]), points[ri])
      if (res === undefined) points.push(G.invalidPoint)
      else points.push(res)
      break
    }
    case 'intersectionCC0': {
      const [_,ci1,ci2] = step
      const res = G.intersectionCC(circles[ci1], circles[ci2])
      if (res.length == 0) points.push(G.invalidPoint)
      else points.push(res[0])
      break
    }
    case 'intersectionCC1': {
      const [_,ci1,ci2] = step
      const res = G.intersectionCC(circles[ci1], circles[ci2])
      if (res.length == 0) points.push(G.invalidPoint)
      else if(res.length == 1) points.push(res[0])
      else points.push(res[1])
      break
    }
    case 'intersectionCCr0': {
      const [_,ci1,ci2,ri] = step
      const res = G.closestPP(G.intersectionCC(circles[ci1],circles[ci2]), points[ri])
      if (res === undefined) points.push(G.invalidPoint)
      else points.push(res)
      break
    }
    case 'intersectionCCr1': {
      const [_,ci1,ci2,ri] = step
      const res = G.furthestPP(G.intersectionCC(circles[ci1],circles[ci2]), points[ri])
      if (res === undefined) points.push(G.invalidPoint)
      else points.push(res)
      break
    }
    case 'footPL': {
      const [_,pi,li] = step
      points.push(G.footPL(points[pi],lines[li]))
      break
    }
    case 'footPPP': {
      const [_,pi1,pi2,pi3] = step
      points.push(G.footPL(points[pi1],G.linePP(points[pi2], points[pi3])))
      break
    }
    case 'footPC0': {
      const [_,pi,ci] = step
      points.push(G.footPC(points[pi],circles[ci]))
      break
    }
    case 'footPC1': {
      const [_,pi,ci] = step
      points.push(G.footOpPC(points[pi],circles[ci]))
      break
    }
    case 'centerC': {
      const [_,ci] = step
      points.push(circles[ci].c)
      break
    }
    case 'arcMidpointCPP': {
      const [_,ci,pi1,pi2] = step
      const arc = G.arcSegmentCPP(circles[ci], points[pi1], points[pi2])
      points.push(G.centerArc(arc))
      break
    }
    case 'linePP': {
      const [_,pi1,pi2] = step
      lines.push(G.linePP(points[pi1], points[pi2]))
      break
    }
    case 'paralineLP': {
      const [_,li,pi] = step
      lines.push(G.linePN(points[pi], lines[li].n))
      break
    }
    case 'paralinePPP': {
      const [_,pi1,pi2,pi3] = step
      const line = G.linePP(points[pi1], points[pi2])
      lines.push(G.linePN(points[pi3], line.n))
      break
    }
    case 'touchpointPC0': {
      const [_,pi,ci] = step
      const touchpoints = G.touchpointsPC(points[pi], circles[ci])
      if (touchpoints.length == 0) points.push(G.invalidPoint)
      else points.push(touchpoints[0])
      break
    }
    case 'touchpointPC1': {
      const [_,pi,ci] = step
      const touchpoints = G.touchpointsPC(points[pi], circles[ci])
      if (touchpoints.length == 0) points.push(G.invalidPoint)
      else if (touchpoints.length == 1) points.push(touchpoints[0])
      else points.push(touchpoints[1])
      break
    }
    case 'tangentAtPC': {
      const [_,pi,ci] = step
      lines.push(G.tangentAtPC(points[pi], circles[ci]))
      break
    }
    case 'perpBisPP': {
      const [_,pi1,pi2] = step
      lines.push(G.perpBis(points[pi1], points[pi2]))
      break
    }
    case 'perplineLP': {
      const [_,li,pi] = step
      lines.push(G.linePN(points[pi], G.vectorL(lines[li])))
      break
    }
    case 'perplinePPP': {
      const [_,pi1,pi2,pi3] = step
      const line = G.linePP(points[pi1],points[pi2])
      lines.push(G.linePN(points[pi3], G.vectorL(line)))
      break
    }
    case 'angIBisPPP': {
      const [_,pi1,pi2,pi3] = step
      lines.push(G.angIBis(points[pi1], points[pi2], points[pi3]))
      break
    }
    case 'angOBisPPP': {
      const [_,pi1,pi2,pi3] = step
      lines.push(G.angOBis(points[pi1], points[pi2], points[pi3]))
      break
    }
    case 'circlePP': {
      const [_,pi1,pi2] = step
      circles.push(G.circleCP(points[pi1], points[pi2]))
      break
    }
    case 'compassCP': {
      const [_,ci,pi] = step
      circles.push(G.circleCR(points[pi], circles[ci].r))
      break
    }
    case 'compassPPP': {
      const [_,pi1,pi2,pi3] = step
      const r = G.distPP(points[pi1],points[pi2])
      circles.push(G.circleCR(points[pi3], r))
      break
    }
    case 'diaCirclePP': {
      const [_,pi1,pi2] = step
      circles.push(G.diaCircle(points[pi1], points[pi2]))
      break
    }
    case 'circumcirclePPP': {
      const [_,pi1,pi2,pi3] = step
      circles.push(G.circumcircle(points[pi1], points[pi2], points[pi3]))
      break
    }
  }
}

export function runSteps (constr : GeoStep[]) : GeoModel {
  const points : G.Point[] = []
  const lines : G.Line[] = []
  const circles : G.Circle[] = []
  for (const step of constr) applyStep(step, points, lines, circles)
  return {
    points: points,
    lines: lines,
    circles: circles,
  }
}
