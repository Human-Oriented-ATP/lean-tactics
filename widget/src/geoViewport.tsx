import React, { useRef, useEffect } from 'react'
import { DraggableCore, DraggableEvent } from 'react-draggable'
import { PreviewObj, equalPreviewObjs, InitToolSpec, ToolState, ToolResult, dummyToolState, toolFunctions } from './geoTool'
import { ToolName } from './toolbox'
import { GeoModel, GeoStep, runSteps } from './geoConstr'
import * as G from './geoObject'

interface GeoViewportProps {
  tool : ToolName
  constr : GeoStep[]
  model : GeoModel
  setConstr (constr : GeoStep[]) : void
  registerCancelCallback (callback : {() : boolean}) : void
}

export function GeoViewport(props : GeoViewportProps) {

  const canvasRef = useRef<HTMLCanvasElement>(null)
  const [centerMap, setCenterMap] = React.useState(G.unitSimMap)
  const centerMapRef = React.useRef<G.SimMap>(G.unitSimMap)
  centerMapRef.current = centerMap
  const centerMapInv = React.useRef<G.SimMap>(G.unitSimMap)
  const pixelToCoor = React.useRef<G.SimMap>(G.unitSimMap)
  const coorToPixel = React.useRef<G.SimMap>(G.unitSimMap)
  const pixelToStaticCoor = React.useRef<G.SimMap>(G.unitSimMap)
  const staticCoorToPixel = React.useRef<G.SimMap>(G.unitSimMap)
  const outerShift = React.useRef<G.Vector>([0,0]) // pixels in document -> pixels in canvas
  const canvasSize = React.useRef<G.Vector>([100,100]) // pixels in document -> pixels in canvas

  const canvasDrag = React.useRef<G.Point | null>(null)

  const toolStateIni = React.useRef<ToolState>(dummyToolState)
  const toolState = React.useRef<ToolState>(toolStateIni.current)
  const [toolPreview, setToolPreview] = React.useState<PreviewObj[]>([])
  const [winWidth, setWinWidth] = React.useState(window.innerWidth)
  const [winHeight, setWinHeight] = React.useState(window.innerHeight)

  function alignPixelCoor(pixel : G.Point, coor : G.Point) {
    setCenterMap(
      G.simMapFrom1P(
        G.simMapP(pixelToStaticCoor.current, pixel),
        coor,
        centerMapRef.current.mul,
        false
      )
    )
  }

  props.registerCancelCallback(() => {
    if (toolState.current === toolStateIni.current)
      return false
    else {
      initTool()
      return true
    }
  })
  function initTool() {
    setToolState(toolFunctions[props.tool]({
      getPixelToCoor:() => { return pixelToCoor.current },
      getCoorToPixel:() => { return coorToPixel.current },
      model: props.model,
      constr: props.constr,
      setConstr: props.setConstr,
      alignPixelCoor: alignPixelCoor
    }))
    toolStateIni.current = toolState.current
  }
  function setToolState(state : ToolState) {
    toolState.current = state
    if (!equalPreviewObjs(toolPreview, state.preview)){
      setToolPreview(state.preview)
    }
  }
  function updateToolState(state : ToolState | ToolResult | undefined) {
    if (state === undefined) initTool()
    else if (state.type == 'state') setToolState(state)
    else {
      if (state.newSteps.length > 0)
        props.setConstr(props.constr.concat(state.newSteps))
      initTool()
    }
  }
  React.useMemo(() => {
    var skip = false
    if (props.tool == 'move' && toolState.current.movingModel !== undefined) {
      skip = true
      const m = toolState.current.movingModel
      if (props.model.points.length != m.points.length) skip = false
      if (props.model.lines.length != m.lines.length) skip = false
      if (props.model.circles.length != m.circles.length) skip = false
    }
    if (!skip) initTool()
  }, [props.tool, props.constr])

  function updateShifts() {
    if (canvasRef.current === null) return
    const rect : DOMRect = canvasRef.current.getBoundingClientRect()
    outerShift.current = [rect.left, rect.top]
    canvasSize.current = [rect.width, rect.height]
    const u = Math.sqrt(rect.height * rect.width)/4
    staticCoorToPixel.current = G.simMapFrom1P(
      G.zeroVec, [rect.width/2, rect.height/2],
      G.realCpx(u), true
    )
    pixelToStaticCoor.current = G.inverseSM(staticCoorToPixel.current)
    centerMapInv.current = G.inverseSM(centerMap)
    pixelToCoor.current = G.composeSM(
      pixelToStaticCoor.current,
      centerMap
    )
    coorToPixel.current = G.composeSM(
      centerMapInv.current,
      staticCoorToPixel.current
    )
  }

  function drawPoint(ctx : CanvasRenderingContext2D, point : G.Point, radius : number = 3) {
    if (!G.validP(point)) return
    const [px,py] = G.simMapP(coorToPixel.current, point)
    ctx.beginPath()
    ctx.arc(px, py, radius, 0, 2 * Math.PI)
    ctx.fill()
  }
  function drawLine(ctx : CanvasRenderingContext2D, line : G.Line) {
    if (!G.validL(line)) line = G.normalizeL(line)
    if (!G.validL(line)) return
    const pixLine = G.simMapL(coorToPixel.current, line)
    const [width, height] = canvasSize.current
    const segment = G.cropLine(pixLine, 0,0, width, height)
    if (segment === null) return
    ctx.beginPath()
    ctx.moveTo(...segment.start)
    ctx.lineTo(...segment.end)
    ctx.stroke()
  }
  function drawCircle(ctx : CanvasRenderingContext2D, circle : G.Circle) {
    if (!G.validC(circle)) return
    const pixCirc = G.simMapC(coorToPixel.current, circle)
    ctx.beginPath()
    ctx.arc(pixCirc.c[0], pixCirc.c[1], pixCirc.r, 0, 2 * Math.PI)
    ctx.stroke()
  }
  function drawSegment(ctx : CanvasRenderingContext2D, segment : G.Segment) {
    if (!G.validSeg(segment)) return
    const pixSegment = G.simMapSeg(coorToPixel.current, segment)
    ctx.beginPath()
    ctx.moveTo(...pixSegment.start)
    ctx.lineTo(...pixSegment.end)
    ctx.stroke()
  }
  function drawArc(ctx : CanvasRenderingContext2D, arc : G.ArcSegment) {
    if (!G.validArc(arc)) return
    const pixArc = G.simMapArc(coorToPixel.current, arc)
    const c = pixArc.circle
    const start = pixArc.start
    const end = pixArc.end
    ctx.beginPath()
    ctx.arc(c.c[0], c.c[1], c.r, start * Math.PI, end * Math.PI)
    ctx.stroke()
  }
  function drawPreviewObj(ctx : CanvasRenderingContext2D, preview : PreviewObj, level : 0|1|2) {
    var pointSize : number
    if (preview.style == 'select') {
      if (level > 0) return
      ctx.fillStyle = '#00ffff'
      ctx.strokeStyle = '#00ffff'
      ctx.setLineDash([])
      ctx.lineWidth = 3
      pointSize = 10
    }
    else if (preview.style == 'helper') {
      if (level == 0) return
      ctx.fillStyle = '#808080'
      ctx.strokeStyle = '#000000'
      ctx.setLineDash([2,2])
      ctx.lineWidth = 2
      pointSize = 3
    }
    else { // preview.style == 'new'
      if (level == 0) return
      ctx.fillStyle = '#000000'
      ctx.strokeStyle = '#008800'
      ctx.setLineDash([])
      ctx.lineWidth = 1
      pointSize = 5
    }
    G.drawableCases<void>(preview.obj, {
      point: (p:G.Point) => {
        if (level != 1){
          drawPoint(ctx, p, pointSize)
          if (preview.style == 'new') {
            ctx.fillStyle = '#00ff00'
            drawPoint(ctx, p)
          }
        }
      },
      line: (l:G.Line) => { if (level != 2) drawLine(ctx, l) },
      circle: (c:G.Circle) => { if (level != 2) drawCircle(ctx, c) },
      segment: (seg:G.Segment) => { if (level != 2) drawSegment(ctx, seg) },
      arcSegment: (arc:G.ArcSegment) => { if (level != 2) drawArc(ctx, arc) },
    })
  }
  function drawPreviewObjs(ctx : CanvasRenderingContext2D, level : 0|1|2) {
    for (const preview of toolPreview) drawPreviewObj(ctx, preview, level)
  }

  function draw(ctx : CanvasRenderingContext2D) {
    if (canvasRef.current === null) return
    const canvas : Element = canvasRef.current
    const { width, height } = canvas.getBoundingClientRect()

    ctx.fillStyle = '#ffffff'
    ctx.beginPath()
    ctx.rect(0, 0, width, height)
    ctx.fill()

    drawPreviewObjs(ctx,0)

    ctx.fillStyle = '#000000'
    for (var point of props.model.points) {
      drawPoint(ctx, point)
    }
    ctx.strokeStyle = '#000000'
    ctx.lineWidth = 1
    ctx.setLineDash([])
    for (var line of props.model.lines) {
      drawLine(ctx, line)
    }
    for (var circle of props.model.circles) {
      drawCircle(ctx, circle)
    }

    drawPreviewObjs(ctx,1)
    drawPreviewObjs(ctx,2)
  }

  function eventPixel(e : MouseEvent | WheelEvent | React.MouseEvent) : G.Point {
    var x = e.clientX
    var y = e.clientY
    const [ox,oy] = outerShift.current
    x = x - ox
    y = y - oy
    return [x,y]
  }

  function onMouseMove(e : React.MouseEvent){
    const pixel = eventPixel(e)
    updateToolState(toolState.current.move(pixel))
  }
  function onDrag(e : DraggableEvent){
    if ('button' in e) {
      const pixel = eventPixel(e)
      if (canvasDrag.current !== null)
        alignPixelCoor(pixel, canvasDrag.current)
      else {
        updateToolState(toolState.current.drag(pixel))
      }
    }
  }

  function onStartDrag(e : DraggableEvent){
    if ('button' in e) {
      const pixel = eventPixel(e)
      if(e.button == 0) {
        updateToolState(toolState.current.press(pixel))
      }
      else if (e.button == 1) {
        const coor = G.simMapP(pixelToCoor.current, pixel)
        canvasDrag.current = coor
      }
      else if (e.button == 2) {
        initTool()
      }
    }
  }
  function onStopDrag(e : DraggableEvent){
    if ('button' in e) {
      if (e.button == 0){
        const pixel = eventPixel(e)
        updateToolState(toolState.current.release(pixel))
      }
      canvasDrag.current = null
    }
  }
  function onWheel(e : WheelEvent){
    const pixel = eventPixel(e)
    const coor = G.simMapP(pixelToCoor.current, pixel)
    const coef = Math.exp(e.deltaY / 1000)
    setCenterMap(
      G.simMapFrom1P(
        G.simMapP(pixelToStaticCoor.current, pixel),
        coor,
        G.mulVec(centerMap.mul, coef),
        false
      )
    )
    e.preventDefault();
  }

  function onResize(e : Event){
    setWinWidth(window.innerWidth)
    setWinHeight(window.innerHeight)
  }

  useEffect(() => {
    
    if (canvasRef.current === null) return
    const canvas : HTMLCanvasElement = canvasRef.current

    canvas.addEventListener('wheel', onWheel)
    window.addEventListener('resize', onResize)
    updateShifts()

    const context = canvas.getContext('2d')
    if (context !== null) draw(context)

    return () => {
      canvas.removeEventListener('wheel', onWheel)
      window.removeEventListener('resize', onResize)
    };
  }, [draw])

  return <DraggableCore
      onStart={onStartDrag}
      onDrag={onDrag}
      onStop={onStopDrag}
      allowAnyClick={true}
    >
    <canvas
      onContextMenu={(e) => {
        e.preventDefault(); // prevent the default behaviour when right clicked
      }}
      width={winWidth-50}
      height={winHeight-200}
      onMouseMove={onMouseMove}
      ref={canvasRef} {...props}
    /></DraggableCore>
}
