import MutableRefObject from 'react'
import { GeoModel, GeoStep, centerFromCoef, getCircleCoef, applyStep } from './geoConstr'
import { ToolName } from './toolbox'
import * as G from './geoObject'

export interface ToolResult {
  type : 'result'
  action : string
  newSteps : GeoStep[]
}
function toolResult (
    action : string,
    newSteps : GeoStep[]
    ) : ToolResult {
  return {
    type : 'result',
    action : action,
    newSteps: newSteps,
  }
}

export interface PreviewObj {
  style : 'select' | 'helper' | 'new'
  obj : G.Drawable
  permanent? : boolean
}
export function equalPreviewObj (p1 : PreviewObj, p2 : PreviewObj) {
  return p1.style == p2.style && G.drawableEqual(p1.obj, p2.obj)
}
export function equalPreviewObjs (p1 : PreviewObj[], p2 : PreviewObj[]) : boolean {
  if (p1 === p2) return true
  if (p1.length != p2.length) return false
  for (var i=0; i < p1.length; i++)
    if (!equalPreviewObj(p1[i], p2[i])) return false
  return true
}

type ToolOutput = ToolState | ToolResult | undefined
export interface ToolState {
  type : 'state'
  press (pixel : G.Point) : ToolOutput
  release (pixel : G.Point) : ToolOutput
  drag (pixel : G.Point) : ToolOutput
  move (pixel : G.Point) : ToolOutput
  preview : PreviewObj[]
  movingModel? : GeoModel // just a hack to not reset the Move tool while changing the construction
}

interface ObjClick<Obj> {
  free : G.Point
  index : number
  obj : Obj
}

interface GeoToolSpec<Subspec> {
  free? (free:G.Point) : Subspec | undefined
  point? (p:ObjClick<G.Point>) : Subspec | undefined
  line? (p:ObjClick<G.Line>) : Subspec | undefined
  circle? (p:ObjClick<G.Circle>) : Subspec | undefined
}
interface SubspecDrag {
  preview? : PreviewObj[]
  unpreview? : PreviewObj[]
  release? : ToolState | ToolResult
}
interface SubspecStd {
  preview? : PreviewObj[]
  unpreview? : PreviewObj[]
  select? : ToolState | ToolResult
  drag? : GeoToolSpec<SubspecDrag>
}

export interface InitToolSpec {
  getPixelToCoor () : G.SimMap
  getCoorToPixel () : G.SimMap
  model : GeoModel
  constr : GeoStep[]
  setConstr (constr : GeoStep[]) : void
  alignPixelCoor (coor : G.Point, pixel : G.Point) : void
}
interface ToolContext {
  init : InitToolSpec
  preview : PreviewObj[]
}

function initTool (spec : InitToolSpec) : ToolContext {
  return { init:spec, preview:[] }
}
function getNumPoints (ctx : ToolContext) : number {
  return ctx.init.model.points.length
}
function getSelectDistance (spec : InitToolSpec) : number {
  return G.simMapDist(spec.getPixelToCoor(), 20)
}

function findSelection<Subspec> (
      ctx : ToolContext,
      pixel : G.Point,
      spec : GeoToolSpec<Subspec>) : [G.Drawable | undefined, Subspec | undefined] {
  const coor = G.simMapP(ctx.init.getPixelToCoor(), pixel)
  const d = getSelectDistance(ctx.init)
  const candPoints : [number,number,G.Point][] = []
  const candLC : [number,number,G.Line | G.Circle][] = []
  if (spec.point !== undefined)
    ctx.init.model.points.forEach((p,i) => {
      if (G.distPP(coor,p) < d) candPoints.push([G.distPP(coor,p),i,p]) })
  if (spec.line !== undefined)
    ctx.init.model.lines.forEach((l,i) => {
      if (G.distPL(coor,l) < d) candLC.push([G.distPL(coor,l),i,l]) })
  if (spec.circle !== undefined)
    ctx.init.model.circles.forEach((c,i) => {
      if (G.distPC(coor,c) < d) candLC.push([G.distPC(coor,c),i,c]) })

  candPoints.sort((a,b) => a[0]-b[0])
  if (spec.point !== undefined)
    for (const [_,i,p] of candPoints) {
      const res = spec.point({ free:coor, index:i, obj:p })
      if (res !== undefined) return [p,res]
    }

  candLC.sort((a,b) => a[0]-b[0])
  if (spec.line !== undefined || spec.circle !== undefined)
    for (const [_,i,cl] of candLC) {
      if ('n' in cl) { // cl is a Line
        if (spec.line !== undefined) {
          const res = spec.line({ free:coor, index:i, obj:cl })
          if (res !== undefined) return [cl,res]
        }
      }
      else { // cl is a circle
        if (spec.circle !== undefined) {
          const res = spec.circle({ free:coor, index:i, obj:cl })
          if (res !== undefined) return [cl,res]
        }
      }
    }

  if (spec.free !== undefined) return [undefined, spec.free(coor)]
  else return [undefined,undefined]
}
function getPreview (
      ctx : ToolContext,
      selected : G.Drawable | undefined,
      subspec : SubspecStd | SubspecDrag | undefined) : PreviewObj[] {
  if (subspec === undefined) return ctx.preview
  if (subspec.preview === undefined &&
      subspec.unpreview === undefined &&
      selected === undefined) return ctx.preview
  const res = ctx.preview.slice() // copy array
  if (selected !== undefined)
    res.push({ style:'select', obj:selected, permanent:true })
  if (subspec.unpreview !== undefined) {
    for (var unpreview of subspec.unpreview)
      for (var i = res.length-1; i >= 0; i--)
        if (equalPreviewObj(res[i], unpreview) ){
          res.splice(i,1)
          break
        }
  }
  if (subspec.preview !== undefined)
    res.push(...subspec.preview)
  return res
}

function toolState (ctx : ToolContext, spec : GeoToolSpec<SubspecStd>) : ToolState {
  const res : ToolState = {
    type : 'state',
    move:(pixel : G.Point) => { // update preview
      const [obj,subspec] = findSelection<SubspecStd>(ctx, pixel, spec)
      res.preview = getPreview(ctx, obj, subspec)
      return res
    },
    press:(pixel : G.Point) => { // click or drag
      const [obj,subspec] = findSelection<SubspecStd>(ctx, pixel, spec)
      if (subspec === undefined) return undefined
      const preview = getPreview(ctx, obj, subspec)

      ctx.preview = preview.filter(p => p.permanent)

      if (subspec.select === undefined){
        if (subspec.drag === undefined) return undefined
        else return startDragState(ctx, pixel, spec)
      }
      else {
        if (subspec.drag === undefined){
          var res : ToolOutput = subspec.select
          if (res && res.type == 'state') res = res.move(pixel)
          return res
        }
        else
          return decideDragState(
            ctx, pixel, preview,
            subspec.select, subspec.drag
          )
      }
    },
    release:(pixel : G.Point) => { return res },
    drag:(pixel : G.Point) => { return res },
    preview:ctx.preview,
  }
  return res
}
function decideDragState(
      ctx : ToolContext,
      startPix : G.Point,
      preview : PreviewObj[],
      onSelect : ToolOutput,
      specDrag : GeoToolSpec<SubspecDrag>) : ToolState {
  const res : ToolState = {
    type : 'state',
    drag:(pixel : G.Point) => {
      if (G.distPP(pixel, startPix) >= 3) {
        return startDragState(ctx, pixel, specDrag)
      }
      else return res
    },
    release:(pixel : G.Point) => {
      if (onSelect && onSelect.type == 'state')
        onSelect = onSelect.move(pixel)
      return onSelect
    },
    press:(pixel : G.Point) => { return res },
    move:(pixel : G.Point) => { return res },
    preview:preview,
  }
  return res
}
function startDragState(
    ctx : ToolContext,
    pixel : G.Point,
    spec:GeoToolSpec<SubspecDrag>) : ToolState {
  const res : ToolState = {
    type : 'state',
    drag:(pixel : G.Point) => {
      const [obj,subspec] = findSelection<SubspecStd>(ctx, pixel, spec)
      res.preview = getPreview(ctx, obj, subspec)
      return res
    },
    release:(pixel : G.Point) => {
      const [obj,subspec] = findSelection<SubspecDrag>(ctx, pixel, spec)
      if (subspec === undefined) return undefined
      const preview = getPreview(ctx, obj, subspec)

      ctx.preview = preview.filter(p => p.permanent)

      var res : ToolOutput = subspec.release
      if (res && res.type == 'state') res = res.move(pixel)
      return res
    },
    press:(pixel : G.Point) => { return res },
    move:(pixel : G.Point) => { return res },
    preview:ctx.preview,
  }
  return res
}

export type Tool = {(spec : InitToolSpec) : ToolState}

export const dummyToolState : ToolState = {
  type : 'state',
  press : (_:G.Point) => { return dummyToolState },
  release : (_:G.Point) => { return dummyToolState },
  move : (_:G.Point) => { return dummyToolState },
  drag : (_:G.Point) => { return dummyToolState },
  preview : [],
}

export function dummyTool(spec : InitToolSpec) : ToolState {
  return dummyToolState
}

export function pointTool(spec : InitToolSpec) : ToolState {
  const ctx = initTool(spec)
  const ori_num_points = getNumPoints(ctx)
  return toolState(ctx, {
    free:(free : G.Point) => { return {
      select: toolResult(
        `new point ${free}`,
        [['point', free]],
      )
    }},
    line:(l1 : ObjClick<G.Line>) => { return {
      select:
        toolResult(
          `new point ${l1.free} on L${l1.index}`,
          [['pointL', G.dotVV(l1.free, G.vectorL(l1.obj)), l1.index]]
        ),
      drag: {
        line:(l2 : ObjClick<G.Line>) => {
          if (G.equalP(l1.obj.n, l2.obj.n)) return
          if (G.equalP(l1.obj.n, G.opVec(l2.obj.n))) return
          const x = G.intersectionLL(l1.obj,l2.obj)
          return {
            preview: [{style:'new', obj:x}],
            release: toolResult(
              `new intersection of L${l1}, L${l2}`,
              [['intersectionLL', l1.index, l2.index]],
            ),
          }
        },
        circle:(c2 : ObjClick<G.Circle>) => {
          const x = G.closestPP(G.intersectionLC(l1.obj, c2.obj), c2.free)
          if (x !== undefined)
            return {
              preview: [{ style:'new', obj:x }],
              release:
                toolResult(
                  `new intersection of L${l1.index}, C${c2.index}`,
                  [['intersectionLC0', l1.index, c2.index]], // TODO: find the right intersection
                  )
            }
        }
      },
    }},
    circle:(c1 : ObjClick<G.Circle>) => { return {
      select:
        toolResult(
          `new point ${c1.free} on C${c1.index}`,
          [['pointC', G.directionPP(c1.obj.c, c1.free), c1.index]],
        ),
      drag: {
        line:(l2 : ObjClick<G.Line>) => {
          const x = G.closestPP(G.intersectionLC(l2.obj, c1.obj), l2.free)
          if (x !== undefined) return {
              preview: [{ style:'new', obj:x }],
              release:
                toolResult(
                  `new intersection of L${c1.index}, L${l2.index}`,
                  [['intersectionLC0', l2.index, c1.index]], // TODO: find the right intersection
                ),
            }},
        circle:(c2 : ObjClick<G.Circle>) => {
          const x = G.closestPP(G.intersectionCC(c1.obj, c2.obj), c2.free)
          if (x !== undefined) return {
            preview: [{ style:'new', obj:x }],
            release:
              toolResult(
                `new intersection of C${c1.index}, C${c2.index}`,
                [['intersectionCC0', c1.index, c2.index]], // TODO: find the right intersection
              )
          }
        },
        free:(free : G.Point) => { // circle center
          if (G.distPP(free, c1.obj.c) <= c1.obj.r)
            return {
              preview:[{style:'new', obj:c1.obj.c}],
              release:
                toolResult(
                  `center of C${c1.index}`,
                  [['centerC', c1.index]],
                ),
            }
        }
      }
    }},
    point:(p1 : ObjClick<G.Point>) => {
      if (p1.index == ori_num_points)
        return { select: toolResult(
          `new intersection`,
          [],
        ) }
      return {
        select: toolState(ctx, {
          free:(free : G.Point) => { return {
            preview:[
              {style:'helper', obj:G.segment(p1.obj, free)},
              {style:'new', obj:G.midpoint(p1.obj, free)}
            ],
          }},
          point:(p2 : ObjClick<G.Point>) => {
            return { // midpoint
              select:
                toolResult(
                  `midpoint of P${p1.index}, P${p2.index}`,
                  [['midpointPP', p1.index, p2.index]],
                ),
              preview:[
                {style:'helper', obj:G.segment(p1.obj, p2.obj)},
                {style:'new', obj:G.midpoint(p1.obj, p2.obj)},
              ],
              drag: { // foot to virtual line
                point:(p3:ObjClick<G.Point>) => {
                  if (G.distPP(p1.obj, p2.obj) == 0) return
                  if (G.distPP(p1.obj, p3.obj) == 0) return
                  if (G.distPP(p2.obj, p3.obj) == 0) return
                  const line = G.linePP(p2.obj, p3.obj)
                  const foot = G.footPL(p1.obj, line)
                  return {
                    preview: [
                      {style:'helper', obj:line},
                      {style:'helper', obj:G.segment(p1.obj, foot)},
                      {style:'new', obj:foot},
                    ],
                    release:
                      toolResult(
                        `foot of P${p1.index}, to P${p2.index}-P${p3.index}`,
                        [['footPPP', p1.index, p2.index, p3.index]],
                      )
                }},
                free:(free : G.Point) => {
                  const line = G.linePP(p2.obj, free)
                  const foot = G.footPL(p1.obj, line)
                  return {
                  preview: [
                    {style:'helper', obj:line},
                    {style:'helper', obj:G.segment(p1.obj, foot)},
                    {style:'new', obj:foot},
                  ]
                }},
              },
          }},
          line:(l2 : ObjClick<G.Line>) => { // foot to line
            const foot = G.footPL(p1.obj, l2.obj)
            if (G.distPP(foot, l2.free) > 0.5 * G.distPL(p1.obj, l2.obj)) return
            return {
              select:
                toolResult(
                  `foot of P${p1.index} to L${l2.index}`,
                  [['footPL', p1.index, l2.index]],
                ),
              preview: [
                { style:'helper', obj:G.segment(p1.obj, foot) },
                { style:'new', obj:foot },
              ]
            }
          },
          circle:(c2 : ObjClick<G.Circle>) => {
            const opPoint = G.footOpPC(p1.obj, c2.obj)
            if (!G.containedPC(p1.obj, c2.obj)) { // foot to circle
              const foot1 = G.footPC(p1.obj, c2.obj)
              const foot2 = G.footOpPC(p1.obj, c2.obj)
              var foot : G.Point
              var action : ToolResult
              if (G.distPP(c2.free, foot1) < G.distPP(c2.free, c2.obj.c)){
                foot = foot1
                action = toolResult(
                  `Foot of P${p1.index} to C${c2.index}`,
                  [['footPC0', p1.index, c2.index]]
                )
              }
              else {
                foot = foot2
                action = toolResult(
                  `Opposite foot of P${p1.index} to C${c2.index}`,
                  [['footPC1', p1.index, c2.index]],
                )
              }
              return {
                select: action,
                preview:[
                  { style:'helper', obj:G.segment(p1.obj, foot) },
                  { style:'new', obj:foot }
                ]
              }
            }
            else if (G.distPP(opPoint, c2.free) < getSelectDistance(ctx.init)) { // opposite point
              return {
                preview:[{ style:'new', obj:opPoint }],
                select: toolResult(
                  `opposite point to ${p1.index} on C${c2.index}`,
                  [['footPC1', p1.index, c2.index]],
                ),
              }
            }
            else { // arc center
              // first select half of the circle
              const v1 = G.vectorPP(c2.obj.c, p1.obj)
              const vf = G.vectorPP(c2.obj.c, c2.free)
              const cw_arc = (G.mulCpx(vf, G.conjCpx(v1))[1] < 0)
              var half_arc : G.ArcSegment
              if (cw_arc) half_arc = G.arcSegmentCPP(c2.obj, opPoint, p1.obj)
              else half_arc = G.arcSegmentCPP(c2.obj, p1.obj, opPoint)
              return {
                unpreview : [{ style:'select', obj:c2.obj }],
                preview : [{ style:'select', obj:half_arc }],
                select : toolState(ctx, { // then select the second point
                  point : (p3:ObjClick<G.Point>) => {
                    if (G.containedPC(p3.obj, c2.obj) && !G.equalP(p1.obj, p3.obj)) {
                      const arc = (cw_arc ? G.arcSegmentCPP(c2.obj, p3.obj, p1.obj)
                                          : G.arcSegmentCPP(c2.obj, p1.obj, p3.obj))
                      return {
                        preview : [
                          {style:'select', obj:arc},
                          {style:'new', obj:G.centerArc(arc)},
                        ],
                        select :
                          cw_arc ?
                            toolResult(
                              `center of arc on C${c2.index} from P${p3.index} to P${p1.index}`,
                              [['arcMidpointCPP', c2.index, p3.index, p1.index]],
                            ) : toolResult(
                              `center of arc on C${c2.index} from P${p1.index} to P${p3.index}`,
                              [['arcMidpointCPP', c2.index, p1.index, p3.index]],
                            )
                      }
                    }
                  },
                  free : (free:G.Point) => {
                    const arc = (cw_arc ? G.arcSegmentCPP(c2.obj, free, p1.obj)
                                        : G.arcSegmentCPP(c2.obj, p1.obj, free))
                    return {
                      preview : [
                        {style:'select', obj:arc},
                        {style:'new', obj:G.centerArc(arc)},
                      ]
                    }
                  },
                })
              }
            }
          },
        })
    }}
  })
}

export function lineTool(spec : InitToolSpec) : ToolState {
  const ctx = initTool(spec)
  return toolState(ctx, {
    line:(l1:ObjClick<G.Line>) => { return { // parallel line to a given line
      select: toolState(ctx, {
        free:(free:G.Point) => {
          const l = G.linePN(free,l1.obj.n)
          return {
            preview : [{ style:'new', obj:l }],
            select : toolResult(
              `free line through ${free} parallel to ${l1.index}`,
              [['paralineL', l.c, l1.index]],
            ),
          }
        },
        point:(p2:ObjClick<G.Point>) => {
          const l = G.linePN(p2.obj, l1.obj.n)
          return {
            preview : [{ style:'new', obj:l }],
            select : toolResult(
              `line through P${p2.index} parallel to ${l1.index}`,
              [['paralineLP', l1.index, p2.index]],
            )
          }
        }
      })
    }},
    point:(p1:ObjClick<G.Point>) => { return { // parallel line to a pair of points
      drag:{
        free:(free:G.Point) => { return {
          preview:[{ style:'helper', obj:G.linePP(p1.obj,free) }]
        }},
        point:(p2:ObjClick<G.Point>) => {
          const line = G.linePP(p1.obj, p2.obj)
          return {
            preview:[{ style:'helper', obj:line, permanent:true }],
            release: toolState(ctx, {
              free:(free:G.Point) => {
                const res = G.linePN(free,line.n)
                return {
                  preview : [{ style:'new', obj:res }],
                  select : toolResult(
                    `free line through ${free} parallel to ${p1.index}-${p2.index}`,
                    [['paralinePP', res.c, p1.index, p2.index]],
                  ),
                }
              },
              point:(p3:ObjClick<G.Point>) => {
                const res = G.linePN(p3.obj, line.n)
                return {
                  preview : [{ style:'new', obj:res }],
                  select : toolResult(
                    `line through P${p3.index} parallel to ${p1.index}-${p2.index}`,
                    [['paralinePPP', p1.index, p2.index, p3.index]],
                  )
                }
              }
            })
          }
        },
      },
      select: toolState(ctx, {   // starting with a point
        free:(free:G.Point) => {
          const line = G.linePP(p1.obj, free)
          return {
            preview:[{style:'new', obj:line}],
            select: toolResult(
              `free line through P${p1.index} with direction ${G.directionL(line)}`,
              [['lineP', G.directionL(line), p1.index]],
            )
          }
        },
        circle:(c2:ObjClick<G.Circle>) => { // tangent to a circle
          function closeEnough(p:G.Point) {
            return G.distPP(
              G.normalizeVec(G.vectorPP(c2.obj.c, c2.free)),
              G.normalizeVec(G.vectorPP(c2.obj.c, p))
            ) < 0.5
          }
          if (G.containedPC(p1.obj, c2.obj)){
            if (closeEnough(p1.obj)) {
              const res = G.tangentAtPC(p1.obj, c2.obj)
              return {
                preview:[{style:'new', obj:res}],
                select: toolResult(
                  `tangent to C${c2.index} at P${p1.index}`,
                  [['tangentAtPC', p1.index, c2.index]],
                ),
              }
            }
          }
          else { // select the right tangent
            const candidates = G.touchpointsPC(p1.obj, c2.obj)
            var touch : G.Point
            var step0 : GeoStep
            const touchIndex : number = getNumPoints(ctx)
            if (candidates.length == 0) return
            if (candidates.length > 1 && G.distPP(candidates[0], c2.free) > G.distPP(candidates[1], c2.free)) {
              touch = candidates[1]
              step0 = ['touchpointPC1', p1.index, c2.index]
            }
            else
              touch = candidates[0]
              step0 = ['touchpointPC0', p1.index, c2.index]
            if (closeEnough(touch)) {
              
              return {
                preview:[
                  {style:'new', obj:touch},
                  {style:'new', obj:G.linePP(p1.obj, touch)},
                ],
                select: toolResult(
                  `tangent to C${c2.index} through P${p1.index} and ${touch}`,
                  [ step0,
                    ['tangentAtPC', touchIndex, c2.index] ],
                ),
              }
            }
          }
        },
        point:(p2:ObjClick<G.Point>) => { // line through 2 points, possibly angle bisector
          const line = G.linePP(p1.obj, p2.obj)
          return {
            preview:[{style:'new', obj:line}],
            select: toolResult(
              `line through P${p1.index}, P${p2.index}`,
              [['linePP', p1.index, p2.index]],
            ),
            drag:{
              free:(free:G.Point) => { return {
                preview:[
                  {style:'helper', obj:line},
                  {style:'helper', obj:G.linePP(p1.obj,free)},
                  {style:'new', obj:G.angIBis(p1.obj,p2.obj,free)}
                ]
              }},
              point:(p3:ObjClick<G.Point>) => { return {
                preview:[
                  {style:'helper', obj:line},
                  {style:'helper', obj:G.linePP(p1.obj,p3.obj)},
                  {style:'new', obj:G.angIBis(p1.obj,p2.obj,p3.obj)}
                ],
                select:{
                  action:`inner angle bisector between P${p1.index}-P${p2.index}, P${p1.index}-P${p3.index}`
                }
              }},
            }
          }
        }
      }),
    }}
  })
}

export function perpLineTool(spec : InitToolSpec) : ToolState {
  const ctx = initTool(spec)
  return toolState(ctx, {
    line:(l1:ObjClick<G.Line>) => { return { // perpendicular to a given line
      select: toolState(ctx, {
        free:(free:G.Point) => {
          const res = G.linePN(free, G.vectorL(l1.obj))
          return {
            preview : [{ style:'new', obj:res }],
            select : toolResult(
              `free line through ${free} perpendicular to ${l1.index}`,
              [['perplineL', res.c, l1.index]],
            ),
          }
        },
        point:(p2:ObjClick<G.Point>) => {
          const res = G.linePN(p2.obj, G.vectorL(l1.obj))
          return {
            preview : [{ style:'new', obj:res }],
            select : toolResult(
              `line through P${p2.index} perpendicular to ${l1.index}`,
              [['perplineLP', l1.index, p2.index]],
            )
          }
        }
      })
    }},
    point:(p1:ObjClick<G.Point>) => { return { // perpendicular to a pair of points
      drag:{
        free:(free:G.Point) => {
          const line = G.linePP(p1.obj, free)
          return {
            preview:[
              { style:'helper', obj:line },
              { style:'new', obj:G.linePV(free, line.n) }
            ]
        }},
        point:(p2:ObjClick<G.Point>) => {
          const line = G.linePP(p1.obj, p2.obj)
          return {
            preview:[
              { style:'helper', obj:line, permanent:true },
              { style:'new', obj:G.linePV(p2.obj, line.n) },
            ],
            release: toolState(ctx, {
              free:(free:G.Point) => {
                const res = G.linePN(free, G.vectorL(line))
                return {
                  preview : [{ style:'new', obj:res }],
                  select : toolResult(
                    `free line through ${free} perpendicular to ${p1.index}-${p2.index}`,
                    [['perplinePP', res.c, p1.index, p2.index]],
                  ),
                }
              },
              point:(p3:ObjClick<G.Point>) => {
                const res = G.linePN(p3.obj, G.vectorL(line))
                return {
                  preview : [{ style:'new', obj:res }],
                  select : toolResult(
                    `line through P${p3.index} perpendicular to ${p1.index}-${p2.index}`,
                    [['perplinePPP', p1.index, p2.index, p3.index]],
                  )
                }
              }
            })
          }
        },
      },
      select: toolState(ctx, { // perpendicular bisector, possibly outer angle bisector
        free:(free:G.Point) => {
          const line = G.linePP(p1.obj, free)
          return {
            preview:[
              {style:'helper', obj:G.segment(p1.obj,free)},
              {style:'new', obj:G.perpBis(p1.obj,free)},
            ],
          }
        },
        point:(p2:ObjClick<G.Point>) => {
          return {
            preview:[
              {style:'helper', obj:G.segment(p1.obj,p2.obj)},
              {style:'new', obj:G.perpBis(p1.obj,p2.obj)},
            ],
            select: toolResult(
              `perpendicular bisector between P${p1.index} and P${p2.index}`,
              [['perpBisPP', p1.index, p2.index]],
            ),
            drag:{
              free:(free:G.Point) => { return {
                preview:[
                  {style:'helper', obj:G.linePP(p1.obj,p2.obj)},
                  {style:'helper', obj:G.linePP(p1.obj,free)},
                  {style:'new', obj:G.angOBis(p1.obj,p2.obj,free)}
                ]
              }},
              point:(p3:ObjClick<G.Point>) => { return {
                preview:[
                  {style:'helper', obj:G.linePP(p1.obj,p2.obj)},
                  {style:'helper', obj:G.linePP(p1.obj,p3.obj)},
                  {style:'new', obj:G.angOBis(p1.obj,p2.obj,p3.obj)}
                ],
                release: toolResult(
                  `outer angle bisector between P${p1.index}-P${p2.index}, P${p1.index}-P${p3.index}`,
                  [['angOBisPPP', p1.index, p2.index, p3.index]],
                )
              }},
            }
          }
        }
      }),
    }}
  })
}

export function circleTool(spec : InitToolSpec) : ToolState {
  const ctx = initTool(spec)
  return toolState(ctx, {
    circle:(c1:ObjClick<G.Circle>) => { return { // radius given by a circle
      select: toolState(ctx, {
        free:(free:G.Point) => { return {
          preview:[{style:'new', obj:G.circleCR(free, c1.obj.r)}],
          select:toolResult(
            `free circle of radius C${c1.index} at ${free}`,
            [['compassC', free, c1.index]],
          ),
        }},
        point:(p2:ObjClick<G.Point>) => { return {
          preview:[{style:'new', obj:G.circleCR(p2.obj, c1.obj.r)}],
          select:toolResult(
            `circle of radius C${c1.index} at P${p2.index}`,
            [['compassCP', c1.index, p2.index]],
          ),
        }}
      })
    }},
    point:(p1:ObjClick<G.Point>) => { return {
      
      drag:{ // radius given by two points
        free:(free:G.Point) => { return {
          preview: [{style:'new', obj:G.circleCP(free,p1.obj)}],
        }},
        point:(p2:ObjClick<G.Point>) => {
          const dist = G.distPP(p1.obj, p2.obj)
          return {
            preview: [
              {style:'helper', obj:G.segment(p1.obj,p2.obj), permanent:true},
              {style:'new', obj:G.circleCP(p2.obj,p1.obj)},
            ],
            release: toolState(ctx, {
              free:(free:G.Point) => { return {
                preview:[{style:'new', obj:G.circleCR(free, dist)}],
                select: toolResult(
                  `free circle of radius P${p1.index}-P${p2.index} at ${free}`,
                  [['compassPP', free, p1.index, p2.index]],
                ),
              }},
              point:(p3:ObjClick<G.Point>) => { return {
                preview:[{style:'new', obj:G.circleCR(p3.obj, dist)}],
                select: toolResult(
                  `circle of radius P${p1.index}-P${p2.index} at P${p3.index}`,
                  [['compassPPP', p1.index, p2.index, p3.index]],
                ),
              }}
            })
        }}
      },
      select: toolState(ctx, {
        free:(free:G.Point) => { return {
          preview: [{style:'new', obj:G.circleCP(p1.obj,free)}],
          select: toolResult(
            `free circle centered at P${p1.index} with radius ${G.distPP(p1.obj,free)}`,
            [['circleP', G.distPP(p1.obj,free), p1.index]],
          ),
        }},
        point:(p2:ObjClick<G.Point>) => { return {
          preview: [{style:'new', obj:G.circleCP(p1.obj,p2.obj)}],
          select: toolResult(
            `circle centered at P${p1.index} through ${p2.index}`,
            [['circlePP', p1.index, p2.index]],
          ),
        }},
        line:(l2:ObjClick<G.Line>) => {
          const foot = G.footPL(p1.obj, l2.obj)
          const footIndex : number = getNumPoints(ctx)
          if (G.distPP(l2.free, foot) < 0.5 * G.distPL(p1.obj, l2.obj))
            return {
              preview: [
                {style:'new', obj:foot},
                {style:'new', obj:G.circleCP(p1.obj,foot)},
              ],
              select: toolResult(
                `circle centered at P${p1.index} touching ${l2.index}`,
                [ ['footPL', p1.index, l2.index],
                  ['circlePP', p1.index, footIndex] ],
              ),
            }
        },
        circle:(c2:ObjClick<G.Circle>) => {
          const foot0 = G.footPC(p1.obj, c2.obj)
          const foot1 = G.footOpPC(p1.obj, c2.obj)
          const footIndex : number = getNumPoints(ctx)
          var step0 : GeoStep
          var foot : G.Point, action
          if (G.distPP(c2.free, foot0) < G.distPP(c2.free, foot1)){
            foot = foot0
            step0 = ['footPC0', p1.index, c2.index]
          }
          else {
            foot = foot1
            step0 = ['footPC1', p1.index, c2.index]
          }
          if (G.distPP(c2.free, foot) < G.distPP(c2.free, c2.obj.c))
            return {
              preview: [
                {style:'new', obj:foot},
                {style:'new', obj:G.circleCP(p1.obj,foot)},
              ],
              select: toolResult(
                `circle centered at P${p1.index} touching C${c2.index}`,
                [step0, ['circlePP', p1.index, footIndex]],
              )
            }
        },
      })
    }},
  })
}

export function circumCircleTool(spec : InitToolSpec) : ToolState {
  const ctx = initTool(spec)
  return toolState(ctx, {
    point:(p1:ObjClick<G.Point>) => { return {
      select: toolState(ctx, {
        free:(free:G.Point) => { // 1 point
          const circle = G.diaCircle(p1.obj, free)
          return {
            preview:[{style:'new', obj:circle}],
            select: toolResult(
              `free circle through P${p1.index} centered at ${circle.c}`,
              [['circumcircleP', G.vectorPP(p1.obj, circle.c), p1.index]],
            )
          }
        },
        point:(p2:ObjClick<G.Point>) => { if (!G.equalP(p1.obj, p2.obj)) return { // 2 points
          preview:[{style:'new', obj:G.diaCircle(p1.obj, p2.obj)}],
          select: toolState(ctx, {
            free:(free:G.Point) => {
              const circle = G.circumcircle(p1.obj, p2.obj, free)
              return {
                preview:[{style:'new', obj:circle}],
                select: toolResult(
                  `free circle through P${p1.index}, P${p2.index} centered at ${circle.c}`,
                  [['circumcirclePP', getCircleCoef(circle, p1.obj, p2.obj), p1.index, p2.index]],
                ),
              }
            },
            point:(p3:ObjClick<G.Point>) => {
              if (G.equalP(p3.obj, p1.obj) || G.equalP(p3.obj, p2.obj))
                return {
                  preview:[{style:'new', obj:G.diaCircle(p1.obj, p2.obj)}],
                  select: toolResult(
                    `circle with diameter P${p1.index}-P${p2.index}`,
                    [['diaCirclePP', p1.index, p2.index]],
                  ),
                }
              else // 3 points
                return {
                  preview:[{style:'new', obj:G.circumcircle(p1.obj, p2.obj, p3.obj)}],
                  select: toolResult(
                    `circle through P${p1.index}, P${p2.index}, P${p3.index}`,
                    [['circumcirclePPP', p1.index, p2.index, p3.index]],
                  ),
                }
            }
          }),
        }},
      })
    }}
  })
}

type MoveFunction<T> = { (grasp : G.Point) : { (m : G.Point) : [G.Point | number, T] } }
type MoveFunctionG = MoveFunction<G.Point | G.Line | G.Circle>

export function moveTool(spec : InitToolSpec) {

  // First prepare MoveFunctions for all movable objects

  const points : G.Point[] = []
  const lines : G.Line[] = []
  const circles : G.Circle[] = []
  const movablePoints : [G.Point, number, MoveFunction<G.Point>][] = []
  const movableLines : [G.Line, number, MoveFunction<G.Line>][] = []
  const movableCircles : [G.Circle, number, MoveFunction<G.Circle>][] = []
  spec.constr.forEach((step,stepI) => {
     applyStep(step, points, lines, circles)
     switch (step[0]) {
      case 'point' : {
        const pi = points.length-1
        const p = spec.model.points[pi]
        movablePoints.push([p, stepI, (_ : G.Point) => (m:G.Point) => {
          return [m,m]
        }])
      break
      }
      case 'pointL' : {
        const [_,__,li] = step
        const l = spec.model.lines[li]
        const pi = points.length-1
        const p = spec.model.points[pi]
        movablePoints.push([p, stepI, (_ : G.Point) => (m:G.Point) => {
          const obj = G.footPL(m, l)
          return [G.dotVV(obj, G.vectorL(l)),obj]
        }])
        break
      }
      case 'pointC' : {
        const [_,__,ci] = step
        const c = spec.model.circles[ci]
        const pi = points.length-1
        const p = spec.model.points[pi]
        movablePoints.push([p, stepI, (_ : G.Point) => (m:G.Point) => {
          const obj = G.footPC(m, c)
          return [G.directionPP(c.c, obj), obj]
        }])
        break
      }
      case 'lineP' : {
        const [_,__,pi] = step
        const p = spec.model.points[pi]
        const li = lines.length-1
        const l = spec.model.lines[li]
        movableLines.push([l, stepI, (_ : G.Point) => (m:G.Point) => {
          const obj = G.linePP(p, m)
          return [G.directionL(obj), obj]
        }])
        break
      }
      case 'paralineL' : {
        const [_,__,li0] = step
        const l0 = spec.model.lines[li0]
        const li = lines.length-1
        const l = spec.model.lines[li]
        movableLines.push([l, stepI, (_ : G.Point) => (m:G.Point) => {
          const obj = G.linePN(m, l0.n)
          return [obj.c, obj]
        }])
        break
      }
      case 'paralinePP' : {
        const [_,__,pi0,pi1] = step
        const p0 = spec.model.points[pi0]
        const p1 = spec.model.points[pi1]
        const li = lines.length-1
        const l = spec.model.lines[li]
        const l0 = G.linePP(p0,p1)
        movableLines.push([l, stepI, (_ : G.Point) => (m:G.Point) => {
          const obj = G.linePN(m, l0.n)
          return [obj.c, obj]
        }])
        break
      }
      case 'perplineL' : {
        const [_,__,li0] = step
        const l0 = spec.model.lines[li0]
        const li = lines.length-1
        const l = spec.model.lines[li]
        movableLines.push([l, stepI, (_ : G.Point) => (m:G.Point) => {
          const obj = G.linePN(m, G.vectorL(l0))
          return [obj.c, obj]
        }])
        break
      }
      case 'perplinePP' : {
        const [_,__,pi0,pi1] = step
        const p0 = spec.model.points[pi0]
        const p1 = spec.model.points[pi1]
        const li = lines.length-1
        const l = spec.model.lines[li]
        const l0 = G.linePP(p0,p1)
        movableLines.push([l, stepI, (_ : G.Point) => (m:G.Point) => {
          const obj = G.linePN(m, G.vectorL(l0))
          return [obj.c, obj]
        }])
        break
      }
      case 'circleP' : {
        const [_,__,pi0] = step
        const p0 = spec.model.points[pi0]
        const ci = circles.length-1
        const c = spec.model.circles[ci]
        movableCircles.push([c, stepI, (_ : G.Point) => (m:G.Point) => {
          const obj = G.circleCP(p0, m)
          return [obj.r, obj]
        }])
        break
      }
      case 'compassC' : {
        const [_,__,ci0] = step
        const c0 = spec.model.circles[ci0]
        const ci = circles.length-1
        const c = spec.model.circles[ci]
        movableCircles.push([c, stepI, (grasp : G.Point) => {
          const graspVec = G.mulVec(G.normalizeVec(G.vectorPP(grasp, c.c)), c.r)
          return (m:G.Point) => {
            const obj = G.circleCR(G.shiftPV(m, graspVec), c0.r)
            return [obj.c, obj]
          }
        }])
        break
      }
      case 'compassPP' : {
        const [_,__,pi0,pi1] = step
        const p0 = spec.model.points[pi0]
        const p1 = spec.model.points[pi1]
        const r = G.distPP(p0,p1)
        const ci = circles.length-1
        const c = spec.model.circles[ci]
        movableCircles.push([c, stepI, (grasp : G.Point) => {
          const graspVec = G.mulVec(G.normalizeVec(G.vectorPP(grasp, c.c)), c.r)
          return (m:G.Point) => {
            const obj = G.circleCR(G.shiftPV(m, graspVec), r)
            return [obj.c, obj]
          }
        }])
        break
      }
      case 'circumcircleP' : {
        const [_,__,pi0] = step
        const p0 = spec.model.points[pi0]
        const ci = circles.length-1
        const c = spec.model.circles[ci]
        movableCircles.push([c, stepI, (grasp : G.Point) => {
          var coef = getCircleCoef(c, p0, G.footPC(grasp,c))
          if (Math.abs(coef) > 10) coef = 0  
          return (m:G.Point) => {
            const center = centerFromCoef(coef, p0, m)
            const obj = G.circleCP(center, p0)
            return [G.vectorPP(p0,center), obj]
          }
        }])
        break
      }
      case 'circumcirclePP' : {
        const [_,__,pi0,pi1] = step
        const p0 = spec.model.points[pi0]
        const p1 = spec.model.points[pi1]
        const ci = circles.length-1
        const c = spec.model.circles[ci]
        movableCircles.push([c, stepI, (_ : G.Point) => (m:G.Point) => {
          const obj = G.circumcircle(p0,p1,m)
          const coef = getCircleCoef(obj, p0, p1)
          return [coef, obj]
        }])
      }
    }
  })

  function getCoor(pixel : G.Point) {
    return G.simMapP(spec.getPixelToCoor(), pixel)
  }
  function findMoveSelection(pixel:G.Point) : undefined | [G.Drawable, number, MoveFunctionG] {
    const coor = getCoor(pixel)
    const d = getSelectDistance(spec)
    const candPoints = movablePoints.filter(([p,pi,f2]) => (G.distPP(coor, p) < d))
    if (candPoints.length > 0) {
      var res : [G.Point, number, MoveFunctionG] = candPoints[0]
      for (var i=1; i < candPoints.length; i++)
        if (G.distPP(coor,candPoints[i][0]) < G.distPP(coor,res[0]))
          res = candPoints[i]
      return res
    }
    var candLine : [G.Line, number, MoveFunctionG] | undefined = undefined
    for (const cand of movableLines) {
      if (G.distPL(coor, cand[0]) < d) {
        if (candLine === undefined) candLine = cand
        else if (G.distPL(coor,cand[0]) < G.distPL(coor,candLine[0]))
          candLine = cand
      }
    }
    var candCircle : [G.Circle, number, MoveFunctionG] | undefined = undefined
    for (const cand of movableCircles) {
      if (G.distPC(coor, cand[0]) < d) {
        if (candCircle === undefined) candCircle = cand
        else if (G.distPC(coor,cand[0]) < G.distPC(coor,candCircle[0]))
          candCircle = cand
      }
    }
    if (candLine === undefined) {
      if (candCircle === undefined) return undefined
      else return candCircle
    }
    else {
      if (candCircle === undefined) return candLine
      else return (
        G.distPL(coor, candLine[0]) < G.distPC(coor, candCircle[0]) ?
        candLine : candCircle
      )
    }
  }

  const res : ToolState = {
    type: 'state',
    move: (pixel:G.Point) => {
      const selection = findMoveSelection(pixel)
      if (selection === undefined) return res
      else {
        const [obj,constrIndex,f] = selection
        res.preview = [{style:'select', obj:obj}]
        return res
      }
    },
    press: (pixel:G.Point) => {
      const selection = findMoveSelection(pixel)
      if (selection == undefined) { // TODO, we could grasp the view
        const coor = getCoor(pixel)
        const moveView : ToolState = {
          type : 'state',
          move : (_) => moveView,
          press : (_) => moveView,
          release : (_) => undefined,
          drag : (pixel : G.Point) => {
            spec.alignPixelCoor(pixel, coor)
            return moveView
          },
          preview : [],
        }
        return moveView
      }
      else {
        const [obj,stepI,f] = selection
        const f2 : {(m:G.Point) : [G.Point | number, G.Point | G.Line | G.Circle]} = f(getCoor(pixel))
        const movingState : ToolState = {
          type : 'state',
          move : (_) => movingState,
          press : (_) => movingState,
          release : (_) => undefined,
          drag : (pixel : G.Point) => {
            const m = getCoor(pixel)
            const [coef2,obj2] = f2(m)
            const constr2 = spec.constr.slice()
            const step2 = spec.constr[stepI].slice()
            step2[1] = coef2
            constr2[stepI] = step2 as GeoStep
            spec.setConstr(constr2)
            movingState.preview = [{ style:'select', obj:obj2 }]
            return movingState
          },
          preview : [{ style:'select', obj:obj }],
          movingModel : spec.model,
        }
        return movingState
      }
    },
    release: (pixel:G.Point) => {
      return res
    },
    drag: (pixel:G.Point) => {
      return res
    },
    preview: []
  }
  return res
}

export const toolFunctions : Record<ToolName, Tool> = {
  point : pointTool,
  line : lineTool,
  perpline : perpLineTool,
  circle : circleTool,
  circumcircle : circumCircleTool,
  move : moveTool,
  hide : dummyTool,
  label : dummyTool,
  derive : dummyTool,
}
