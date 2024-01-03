import MotivatedMoves.GUI.SVGTree
import ProofWidgets

namespace TreeRender

open Lean Widget ProofWidgets Server

private structure TextBubbleParams where
  /-- The approximate width, in pixels, of a Unicode character in the chosen font. -/
  charWidth : Nat := 8
  /-- The amount of horizontal padding to add around text in text bubbles. -/
  padding : Nat := 4
  /-- The height of the background bubble surrounding a textbox in pixels. -/
  height : Nat := 20
  /-- The rounding of the text bubble (i.e., the value of the parameters `rx` and `ry` of `rect`). -/
  rounding : Nat := 10
  /-- The opacity of the text bubble. -/
  opacity : Float := 0.5

private structure BackgroundFrameParams where
  /-- The default background color. -/
  bgColor : Svg.Color := (0.75, 0.75, 0.75)
  /-- The default opacity of the background of a frame. -/
  bgOpacity : Float := 0.7
  /-- The default rounding of the background rectangle. -/
  bgRounding : Nat := 10
  /-- The highlight stroke width of the background rectangle border. -/
  bgStrokeWidth : Nat := 3
  /-- The highlight color of the background rectangle border. -/
  bgStrokeColor : Svg.Color := (0.2, 0.6, 1.0)

private structure TreeRenderParams extends TextBubbleParams, BackgroundFrameParams where
  /-- The number of pixels occupied by each row in the tree display. -/
  rowSize : Nat := 30
  /-- The list of selected locations in the rendered proof state. -/
  selectedLocations : Array SubExpr.Pos
  /-- The current frame in the SVG. -/
  frame : Svg.Frame
  /-- The color of the current frame. -/
  color : Svg.Color
  /-- The current position within the expression being rendered. -/
  pos : SubExpr.Pos := .root

private structure TreeRenderState where
  /-- The elements of the final SVG output. -/
  elements : Array Html := #[]

/-- A monad for rendering a proof tree as an SVG. -/
private abbrev TreeRenderM := StateT TreeRenderState (ReaderM TreeRenderParams)

section LensNotation

-- From Jovan's Zulip thread https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Lens-like.20notation/near/409670188

syntax ident "%~" : term
syntax ident "%~" term : term
macro_rules
| `($n:ident %~ $f $x) => `({ $x with $n:ident := $f $x.$n })
| `($n:ident %~ $f) => `(fun x => { x with $n:ident := $f x.$n })
| `($n:ident %~) => `(fun f x => { x with $n:ident := f x.$n })

end LensNotation

/-- Add a new SVG element. -/
def draw (element : Html) : TreeRenderM Unit :=
  modify fun σ ↦ { σ with elements := σ.elements.push element }

/-- Modify the current frame to start on the next row. -/
def withNextRow (act : TreeRenderM α) : TreeRenderM α := do
  let ρ ← read
  withReader (frame %~ height %~ (· - ρ.rowSize)) act

/-- Modify the background color of the current frame. -/
def withColor (c : Svg.Color) : TreeRenderM α → TreeRenderM α :=
  withReader ({ · with color := c })

/-- Use a different frame. -/
def withFrame (f : Svg.Frame) : TreeRenderM α → TreeRenderM α :=
  withReader ({ · with frame := f })

/-- Move down the expression tree. -/
def descend (childIdx : Nat) : TreeRenderM α → TreeRenderM α := 
  withReader (pos %~ (·.push childIdx))

/-- Split a frame into left and right halves. -/
def splitFrameHorizontal (f : Svg.Frame) : Svg.Frame × Svg.Frame := 
  ( { f with xSize := f.xSize / 2, width := f.width / 2 }, 
    { f with xSize := f.xSize / 2, width := f.width / 2, xmin := f.xmin + f.xSize / 2 })

/-- Checks if the current position is selected. -/
def isSelected : TreeRenderM Bool := do
  let ρ ← read
  return ρ.selectedLocations.contains ρ.pos

/-- Draw a rectangle bounding the current frame, set to highlight when 
    the current position is selected in the UI. -/
def drawFrame : TreeRenderM Unit := do
  let ρ ← read
  draw <| .element "rect" (#[
    ("x", toJson ρ.frame.xmin),
    ("y", toJson ρ.frame.ymin),
    ("width", toJson ρ.frame.width),
    ("height", toJson ρ.frame.height),
    ("fill", ρ.color.toStringRGB),
    ("opacity", toJson ρ.bgOpacity),
    ("rx", toJson ρ.bgRounding)
  ].append <|
  if (← isSelected) then
    -- highlighting when the associated position is selected
    #[("stroke-width", toJson ρ.bgStrokeWidth), ("stroke", toJson ρ.bgStrokeColor)]
  else #[]) #[]

open scoped Jsx in
/-- Draw a piece of interactive code at the centre of the top row of the current frame and go to the next row. -/
def drawCode (code : CodeWithInfos) (color : Svg.Color) : TreeRenderM Unit := do
  let ρ ← read
  let codeLength := ρ.charWidth * code.pretty.length
  let (x, y) := (ρ.frame.width / 2 - codeLength / 2, ρ.frame.height - (← read).rowSize / 2 + ρ.height / 2)
  draw <| .element "rect" #[
    ("x", x),
    ("y", y),
    ("width", codeLength + 2 * ρ.padding),
    ("height", ρ.height),
    ("rx", ρ.rounding),
    ("fill", color.toStringRGB),
    ("opacity", toJson ρ.opacity)
  ] #[]
  draw <| .element "foreignObject" #[
    ("x", x + ρ.padding),
    ("y", y),
    ("width", codeLength),
    ("height", ρ.height)
  ] #[<InteractiveCode fmt={code} />]