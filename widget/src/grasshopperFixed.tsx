import React, { useRef, useState, useEffect } from 'react'
import { DraggableCore, DraggableEvent } from 'react-draggable'

type PreviewObj = ['square', number] | ['jump', number] | ['freejump', number,number]

function previewDifferent(a : PreviewObj, b : PreviewObj) {
  if (a[0] != b[0]) return true
  switch (a[0]) {
    case "square":
    case "jump": {
      return a[1] != b[1]
    }
    case "freejump": {
      return a[1] != b[1] || a[2] != b[2]
    }
  }
}
function previewsDifferent(a : PreviewObj[], b : PreviewObj[]) : boolean {
  if (a.length !== b.length) return true
  for (var i=0; i<a.length; i++)
    if (previewDifferent(a[i], b[i])) return true
  return false
}

type ToolState = {(pos : [number,number]) : undefined | {
  click? : {() : ToolState | undefined}
  drag? : {() : ToolDragState}
  preview? : PreviewObj[]
}}
const dummyToolState : ToolState = (coor) => undefined

type ToolDragState = {(pos : [number,number]) : undefined | {
  release? : {() : ToolState | undefined}
  preview? : PreviewObj[]
}}
type MouseDragEvent = MouseEvent | React.MouseEvent<HTMLElement | SVGElement, MouseEvent>
interface DragStateLowlevel {
  drag (e : MouseDragEvent) : void
  release (e : MouseDragEvent) : void
}

function cumsum(l : number[]) : number[] {
  var s = 0
  const res = []
  for (const x of l) {
    res.push(s)
    s += x
  }
  res.push(s)
  return res
}

interface ToolData {
  jumpsRef : React.MutableRefObject<number[]>
  landingsRef : React.MutableRefObject<number[]>
  minesRef : React.MutableRefObject<Set<number>>
  numSquaresRef : React.MutableRefObject<number>
  setJumps (jumps : number[]) : void
  setMines (mines : Set<number>) : void
}

function initToolState(data : ToolData) : ToolState {
  return (coor : [number,number]) => {
    const jumps = data.jumpsRef.current
    const landings = data.landingsRef.current
    const mines = data.minesRef.current
    const numSquares = data.numSquaresRef.current
    const [x,y] = coor
    if (y < -1 || y > 1) return
    if (y < 0) {
      if (x+0.5 >= 0) {
        for (var j = 0; j < jumps.length; j++) {
          if (landings[j+1] > x+0.5) {
            return {
              drag: () => {
                const pos : number[] = []
                const rest = jumps.slice(0,j).concat(jumps.slice(j+1))
                const jval = jumps[j]
                const startRel = landings[j]-x
                const endRel = landings[j+1]-x
                for (var j2 = 0; j2 < jumps.length; j2++) {
                  if (j2 <= j)
                    pos.push(landings[j2] + x-landings[j])
                  else
                    pos.push(landings[j2+1] + x-landings[j+1])
                }
                return ((coor2:[number,number]) => {
                  const [x2,y2] = coor2
                  var best = 0
                  for (j2=1; j2 < jumps.length; j2++) {
                    if (Math.abs(pos[j2] - x2) < Math.abs(pos[best] - x2))
                      best = j2
                  }
                  const jumps2 = rest.slice()
                  jumps2.splice(best, 0, jval)
                  data.setJumps(jumps2)
                  return {
                    preview: [
                      ['jump', best],
                      ['freejump', startRel+x2, endRel+x2],
                    ]
                  }
                })
              },
              preview: [['jump', j]]
            }
          }
        }
      }
    }
    else {
      var i = Math.floor(x)
      if (i >= 0 && i < numSquares) {
        const sgn = x-i > 0.5 ? 1 : -1
        var i1 : number | null = null
        for (var d=0; d < numSquares; d++) {
          if (mines.has(i+sgn*d)) {
            i1 = i+sgn*d
            break
          }
          if (mines.has(i-sgn*d)) {
            i1 = i-sgn*d
            break
          }
        }
        const preview : PreviewObj[] = [['square', i]]
        if (i1 === null) return {
          preview: preview,
        }
        if (i1 != i) preview.push(['square', i1])
        return {
          preview: preview,
          drag: () => {
            const last : number[] = []
            if (i1 !== null) last.push(i1)
            const minesRest = new Set(mines)
            if (i1 !== null) minesRest.delete(i1)
            return (coor : [number,number]) => {
              const i2 = Math.floor(coor[0])
              const numSquares = data.numSquaresRef.current
              if (i2 != last[0] && i2 >= 0 && i2 < numSquares && !minesRest.has(i2)) {
                const minesNext = new Set(minesRest)
                minesNext.add(i2)
                last[0] = i2
                data.setMines(minesNext)
              }
              return {
                preview: [['square', last[0]]],
              }
            }
          }
        }
      }
    }
  }
}

interface ViewProps {
  jumpsRef : React.MutableRefObject<number[]>
  landingsRef : React.MutableRefObject<number[]>
  minesRef : React.MutableRefObject<Set<number>>
  numSquaresRef : React.MutableRefObject<number>
  setJumps (jumps : number[]) : void
  setMines (mines : Set<number>) : void
}

function View(props : ViewProps) {
  const canvasRef = useRef<HTMLCanvasElement>(null)
  const [preview,setPreviewState] = useState<PreviewObj[]>([])
  const previewRef = useRef<PreviewObj[]>(preview)
  previewRef.current = preview
  const jumps = props.jumpsRef.current
  const landings = props.landingsRef.current
  const mines = props.minesRef.current
  const numSquares = props.numSquaresRef.current
  const sceneWidth = numSquares+1

  const toolState = useRef<ToolState>(dummyToolState)
  const dragState = useRef<DragStateLowlevel | null>(null)

  function setPreview(nextPreview : PreviewObj[] | undefined) {
    const nextPreviewValid = nextPreview ?? []
    if (previewsDifferent(previewRef.current, nextPreviewValid)) {
      setPreviewState(nextPreviewValid)
    }
  }

  function initTool() {
    setPreview([])
    toolState.current = initToolState({
      jumpsRef: props.jumpsRef,
      landingsRef: props.landingsRef,
      minesRef: props.minesRef,
      numSquaresRef: props.numSquaresRef,
      setJumps: props.setJumps,
      setMines: props.setMines,
    })
    dragState.current = null
  }

  React.useMemo(initTool, [])

  function eventCoor(e : MouseEvent | WheelEvent | React.MouseEvent) : [number,number] {
    var x = e.clientX
    var y = e.clientY
    if (canvasRef.current === null) return [x,y]
    const rect : DOMRect = canvasRef.current.getBoundingClientRect()
    x -= (rect.left + rect.right)/2
    y -= (rect.top + rect.bottom)/2
    const scale = rect.width / sceneWidth
    x /= scale
    y /= scale
    x += numSquares/2
    return [x,y]
  }
  function onDrag(e : DraggableEvent){
    if (!('button' in e)) return
    if (dragState.current == null) return
    dragState.current.drag(e)
  }
  function onStartDrag(e : DraggableEvent){
    if (!('button' in e)) return
    if (dragState.current !== null) return
    const coor = eventCoor(e)
    const state = toolState.current(coor) ?? {}

    function startDrag() {
      if (state.drag === undefined) return
      const stateD = state.drag() ?? {}
      setPreview((stateD(coor) ?? {}).preview)
      dragState.current = {
        drag : (e : MouseDragEvent) => {
          const coor2 = eventCoor(e)
          setPreview((stateD(coor2) ?? {}).preview)
        },
        release : (e : MouseDragEvent) => {
          const coor2 = eventCoor(e)
          const stateRes = stateD(coor2) ?? {}
          if (stateRes.release === undefined){
            initTool()
            return
          }
          const nextState = stateRes.release()
          if (nextState === undefined) initTool()
          else toolState.current = nextState
        }
      }
    }
    function click() {
      if (state.click === undefined) return
      const nextState = state.click()
      if (nextState === undefined) initTool()
      else toolState.current = nextState
    }
    if (state.drag === undefined) {
      if (state.click === undefined) {
        initTool()
      }
      else {
        click()
      }
    }
    else {
      if (state.click === undefined) {
        startDrag()
      }
      else {
        dragState.current = {
          drag : (e2 : MouseDragEvent) => {
            if ((e.clientX - e2.clientX) ** 2 + (e.clientY - e2.clientY) ** 2 < 9)
              startDrag()
          },
          release : (e2 : MouseDragEvent) => {
            click()
          }
        }
      }
    }
  }
  function onStopDrag(e : DraggableEvent){
    if (!('button' in e)) return
    if (dragState.current == null) return
    const coor = eventCoor(e)
    dragState.current.release(e)
    dragState.current = null
  }
  function onMouseMove(e : React.MouseEvent){
    if (dragState.current !== null) return
    const coor = eventCoor(e)
    setPreview((toolState.current(coor) ?? {}).preview)
  }

  function drawJump(ctx : CanvasRenderingContext2D, start : number, end : number) {
    const y = 0.7
    ctx.beginPath()
    ctx.moveTo(start-0.5, 0)
    ctx.bezierCurveTo(start-0.25, -y, start-0.25, -y, start, -y)
    ctx.lineTo(end-1, -y)
    ctx.bezierCurveTo(end-0.75, -y, end-0.75, -y, end-0.5, 0)
  }
  function drawMine(ctx : CanvasRenderingContext2D, m : number) {
    ctx.beginPath()
    ctx.arc(0.5+m, 0.5, 0.3, 0, 2 * Math.PI)
    ctx.closePath()
    ctx.fillStyle = '#000000'
    ctx.fill()
  }
  function drawSquare(ctx : CanvasRenderingContext2D, i : number) {
    ctx.beginPath()
    ctx.rect(0+i, 0, 1, 1)
    ctx.closePath()
  }
  function drawPreview(ctx : CanvasRenderingContext2D, obj : PreviewObj) {
    if (obj[0] == 'square') {
      const [_,i] = obj
      drawSquare(ctx, i)
      ctx.fillStyle = '#00ffff'
      ctx.fill()
    }
    else if (obj[0] == 'jump'){
      const [_,i] = obj
      drawJump(ctx, landings[i], landings[i+1])
      ctx.fillStyle = '#00ffff'
      ctx.fill()
    }
    else if (obj[0] == 'freejump'){
      const [_,start,end] = obj
      ctx.save()
      ctx.translate(0,-0.5)
      drawJump(ctx, start, end)
      ctx.lineWidth = 0.1
      ctx.strokeStyle = '#999999'
      // ctx.setLineDash([2,2])
      ctx.stroke()
      ctx.restore()
    }
  }
  function draw(ctx : CanvasRenderingContext2D) {
    ctx.strokeStyle = '#000000'
    ctx.lineWidth = 0.05
    for (const obj of preview) {
      drawPreview(ctx, obj)
    }
    for (var i=0; i < numSquares; i++) {
      drawSquare(ctx,i)
      ctx.stroke()
    }
    mines.forEach(mine => drawMine(ctx, mine))
    ctx.lineWidth = 0.1
    ctx.strokeStyle = '#000000'
    for (var i=0; i<jumps.length; i++) {
      drawJump(ctx, landings[i], landings[i+1])
      ctx.stroke()
    }
  }

  useEffect(() => {    
    if (canvasRef.current === null) return
    const canvas : HTMLCanvasElement = canvasRef.current

    const ctx = canvas.getContext('2d')
    if (ctx !== null) {
      const { width, height } = canvas.getBoundingClientRect()
      const scale = width / sceneWidth

      ctx.resetTransform()
      ctx.fillStyle = '#ffffff'
      ctx.beginPath()
      ctx.rect(0, 0, width, height)
      ctx.closePath()
      ctx.fill()
      ctx.translate(width/2, height/2)
      ctx.scale(scale, scale)
      ctx.translate(-numSquares/2, 0)
      draw(ctx)
    }
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
      width={500}
      height={200}
      onMouseMove={onMouseMove}
      ref={canvasRef} {...props}
    /></DraggableCore>
}

function fixMines(mines : Set<number>, numSquares : number, numMines : number) {
  var minesL = Array.from(mines)
  if (minesL.length == numMines && minesL.every(m => (m < numSquares)))
    return mines
  minesL = minesL.filter(m => (m < numSquares))
  if (minesL.length > numMines) {
    minesL.sort()
    minesL.splice(numMines)
  }
  else if (minesL.length < numMines) {
    for (var i = numSquares-1; i >= 0 && minesL.length < numMines; i--)
      if (!mines.has(i)) minesL.push(i)
  }
  return new Set(minesL)
}

function findDups(l : number[]) : Set<number> {
  const elems = new Set<number>()
  const res = new Set<number>()
  for (const x of l) {
    if (elems.has(x)) res.add(x)
    else elems.add(x)
  }
  return res
}

interface GrasshopperFixedProps {
  jumps : number[]
}

function GrasshopperFixed(props : GrasshopperFixedProps) {
  const [jumps, setJumpsState] = useState(props.jumps)
  const landings = cumsum(jumps)
  const numSquares = jumps.reduce((a, b) => a + b, 0)-1
  const [mines, setMines] = useState<Set<number>>(new Set())

  const jumpsRef = useRef<number[]>(jumps)
  jumpsRef.current = jumps
  const landingsRef = useRef<number[]>(landings)
  landingsRef.current = landings
  const minesRef = useRef<Set<number>>(mines)
  const numSquaresRef = useRef<number>(numSquares)
  numSquaresRef.current = numSquares
  minesRef.current = fixMines(mines, numSquares, jumps.length-1)

  const inputElements = useRef<(HTMLInputElement | null)[]>([])
  function setInputElement(i : number, elem : HTMLInputElement | null) {
    console.log(`setInputElement ${i}`)
    console.log(elem)
    while (i >= inputElements.current.length)
      inputElements.current.push(null)
    inputElements.current[i] = elem
  }
  function getInputElement(i : number) : HTMLInputElement | null {
    if (i >= inputElements.current.length) return null
    else return inputElements.current[i]
  }
  function setJumps(jumps : number[]) {
    setJumpsState(jumps)
    jumps.forEach((jump,index) => {
      const elem = getInputElement(index)
      console.log(`Elem ${index}`)
      console.log(elem)
      if (elem === null) return
      if (jump != Number(elem.value))
        elem.value = jump.toString()
    })
  }
  function changeJump(index : number, e : React.ChangeEvent<HTMLInputElement>) {
    const jumpsNext = jumps.slice()
    if (index >= jumps.length) return
    const jump = Number(e.target.value)
    if (jumps[index] == jump) return
    jumpsNext[index] = jump
    setJumpsState(jumpsNext)
  }
  function addJump() {
    const jumpS = new Set(jumps)
    var jump = 1
    while (jumpS.has(jump)) jump++
    const jumpsNext = jumps.slice()
    jumpsNext.push(jump)
    setJumps(jumpsNext)
  }
  function removeJump() {
    if (jumps.length == 1) return
    const jumpsNext = jumps.slice()
    jumpsNext.pop()
    setJumps(jumpsNext)
  }
  const dups = findDups(jumps)

  return <div>
    <button onClick={addJump}>Add</button>
    <button onClick={removeJump}>Del</button>
    {
      jumps.map((jump,index) => {
        const style : React.CSSProperties = {width:'40px'}
        if (dups.has(jump)) style.backgroundColor = '#ff9999'
        return <input
          style={style}
          type="number"
          min="1"
          ref={(elem) => setInputElement(index, elem)}
          defaultValue={jump}
          onChange={e => changeJump(index, e)}
          />
      })
    }
    <View
      jumpsRef={jumpsRef}
      landingsRef={landingsRef}
      minesRef={minesRef}
      numSquaresRef={numSquaresRef}
      setJumps={setJumps}
      setMines={setMines}
    />
  </div>
}

export default GrasshopperFixed
