import MotivatedMoves.GUI.DisplayTree
import ProofWidgets

namespace TreeRender

open Lean Widget ProofWidgets Server

-- TODO: Clean up color rendering
private structure TextBubbleColorParams where
  /-- The `forall` nodes in the `DisplayTree` are colored `green`. -/
  forallQuantifierColor : Svg.Color := (0.0, 0.8, 0.4)
  /-- The `exists` nodes in the `DisplayTree` are colored `purple`. -/
  existsQuantifierColor : Svg.Color := (0.4, 0.4, 1.0)
  /-- The `instance` nodes in the `DisplayTree` are colored `gray`. -/
  instanceColor : Svg.Color := (0.5, 0.5, 0.5)
  /-- The `implication` nodes in the `DisplayTree` are colored `orange`. -/
  implicationColor : Svg.Color := (1.0, 0.6, 0.2)
  /-- The `conjunction` nodes in the `DisplayTree` are colored `blue`. -/
  conjunctionColor : Svg.Color := (0.2, 0.6, 1.0)
  /-- The `negation` nodes in the `DisplayTree` are colored `red`. -/
  negationColor : Svg.Color := (0.8, 0.2, 0.0)
  /-- The `nodes` in the `DisplayTree` are colored `light blue` -/
  nodeColor : Svg.Color := (0.0, 0.6, 0.8)

private structure TextBubbleParams extends TextBubbleColorParams where
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
  rowHeight : Nat := 30
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
  modify (elements %~ (·.push element))

/-- Modify the background color of the current frame. -/
def withColor (c : Svg.Color) : TreeRenderM α → TreeRenderM α :=
  withReader ({ · with color := c })

/-- Use a different frame. -/
def withFrame (f : Svg.Frame) : TreeRenderM α → TreeRenderM α :=
  withReader ({ · with frame := f })

/-- Move down the expression tree. -/
def descend (childIdx : Nat) : TreeRenderM α → TreeRenderM α := 
  withReader (pos %~ (·.push childIdx))

/-- Split the current frame into left and right parts and work on them individually. -/
def withHorizontalSplit (width : Nat) 
    (leftAct : TreeRenderM Unit) (rightAct : TreeRenderM Unit) : TreeRenderM Unit := do
  let (leftFrame, rightFrame) := splitFrameHorizontal (← read).frame width
  withFrame leftFrame leftAct
  withFrame rightFrame rightAct
where
  /-- Split a frame into left and right parts. -/
  splitFrameHorizontal (f : Svg.Frame) (width : Nat) : Svg.Frame × Svg.Frame :=
    let size := f.pixelSize * width.toFloat 
    ( { f with xSize := size, width := width }, 
      { f with xSize := f.xSize - size, width := f.width - width, xmin := f.xmin + size } )

/-- Split the current frame into equally sized left and right halves and work on them individually. -/
abbrev withEvenHorizontalSplit (leftAct : TreeRenderM Unit) (rightAct : TreeRenderM Unit) : TreeRenderM Unit := do
  withHorizontalSplit ((← read).frame.width / 2) leftAct rightAct

/-- Split the current frame into top and bottom parts and work on them individually. -/
def withVerticalSplit (height : Nat)
    (topAct : TreeRenderM Unit) (bottomAct : TreeRenderM Unit) : TreeRenderM Unit := do
  let (topFrame, bottomFrame) := splitFrameVertical (← read).frame height
  withFrame topFrame topAct
  withFrame bottomFrame bottomAct
where
  /-- Split a frame into top and bottom parts. -/
  splitFrameVertical (f : Svg.Frame) (height : Nat) : Svg.Frame × Svg.Frame :=
    let size := f.pixelSize * height.toFloat
    ( { f with ymin := f.ymax - size, height := height }, 
      { f with height := f.height / 2 } )

/-- Work on the top row of the current frame and specify what to do on the rest. -/
abbrev withTopRowSplit (rowAct : TreeRenderM Unit) (restAct : TreeRenderM Unit) : TreeRenderM Unit := do
  withVerticalSplit (← read).rowHeight rowAct restAct

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
/-- Draw a piece of interactive code at the center of the current frame. -/
def drawCode (code : CodeWithInfos) (color : Svg.Color) : TreeRenderM Unit := do
  let ρ ← read
  let codeLength := ρ.charWidth * code.pretty.length
  let (x, y) := (ρ.frame.width / 2 - codeLength / 2, ρ.frame.height / 2 + ρ.height / 2)
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
  ] #[< InteractiveCode fmt={code} />]

/--

Render a `DisplayTree` as an SVG image within the `TreeRenderM` monad.

# TO-DO:
- Coloring based on polarity
- A button within each box to select the entire expression contained within

-/
def Tree.DisplayTree.renderCore (displayTree : Tree.DisplayTree) : TreeRenderM Unit := do
  let ρ ← read
  drawFrame
  match displayTree with
  | .forall quantifier name type body =>
    withTopRowSplit
      (drawCode (.append #[quantifier, name, type]) ρ.forallQuantifierColor)
      (descend 1 <| renderCore body) 
  | .exists quantifier name type body =>
    withTopRowSplit
      (drawCode (.append #[quantifier, name, type]) ρ.existsQuantifierColor)
      (descend 1 <| renderCore body)
  | .instance inst body =>
    withTopRowSplit
      (drawCode inst ρ.instanceColor)
      (descend 1 <| renderCore body)
  | .implication antecedent arrow consequent => 
    withVerticalSplit (antecedent.depth * ρ.rowHeight)
      (descend 0 <| withColor ρ.implicationColor <| renderCore antecedent)
      (withTopRowSplit
        (drawCode arrow ρ.implicationColor)
        (descend 1 <| renderCore consequent))
  | .and first wedge second =>
    withTopRowSplit
      (drawCode wedge ρ.conjunctionColor)
      (withEvenHorizontalSplit 
        (descend 0 <| withColor ρ.conjunctionColor <| renderCore first)
        (descend 1 <| withColor ρ.conjunctionColor <| renderCore second))
  | .not neg body =>
    withTopRowSplit
      (drawCode neg ρ.negationColor)
      (descend 1 <| withColor ρ.negationColor <| renderCore body)
  | .node val => 
    withTopRowSplit
      (drawCode val ρ.nodeColor)
      (pure ())