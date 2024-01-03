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

private structure TreeRenderState where
  /-- The current frame in the SVG. -/
  frame : Svg.Frame
  /-- The color of the current frame. -/
  color : Svg.Color
  /-- The current position within the expression being rendered. -/
  pos : SubExpr.Pos := .root
  /-- The elements of the final SVG output. -/
  elements : Array Html := #[]

/-- A monad for rendering a proof tree as an SVG. -/
private abbrev TreeRenderM := ReaderT TreeRenderParams (StateM TreeRenderState)

/-- Add a new SVG element. -/
def draw (element : Html) : TreeRenderM Unit :=
  modify fun σ ↦ { σ with elements := σ.elements.push element }

/-- Checks if a position of the expression is selected. -/
def isSelected (pos : SubExpr.Pos) : TreeRenderM Bool := do
  return (← read).selectedLocations.contains pos

/-- Draw a rectangle bounding the current frame, set to highlight when 
    the current position is selected in the UI. -/
def drawFrame : TreeRenderM Unit := do
  let ρ := (← read).toBackgroundFrameParams 
  let σ ← get
  draw <| .element "rect" (#[
    ("x", toJson σ.frame.xmin),
    ("y", toJson σ.frame.ymin),
    ("width", toJson σ.frame.width),
    ("height", toJson σ.frame.height),
    ("fill", σ.color.toStringRGB),
    ("opacity", toJson ρ.bgOpacity),
    ("rx", toJson ρ.bgRounding)
  ].append <|
  if (← isSelected σ.pos) then
    -- highlighting when the associated position is selected
    #[("stroke-width", toJson ρ.bgStrokeWidth), ("stroke", toJson ρ.bgStrokeColor)]
  else #[]) #[]

open scoped Jsx in
/-- Draw a piece of interactive code at the centre of the top row of the current frame. -/
def drawCode (code : CodeWithInfos) (color : Svg.Color) : TreeRenderM Unit := do
  let ρ := (← read).toTextBubbleParams
  let σ ← get  
  let codeLength := ρ.charWidth * code.pretty.length
  let (x, y) := (σ.frame.width / 2 - codeLength / 2, σ.frame.height - (← read).rowSize / 2 + ρ.height / 2)
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