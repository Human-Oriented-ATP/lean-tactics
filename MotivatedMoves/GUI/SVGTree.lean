import MotivatedMoves.GUI.DisplayTree
import ProofWidgets

open Lean Widget ProofWidgets Server

namespace TreeRender

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
  charWidth : Nat := Tree.charWidth
  /-- The amount of horizontal padding to add around text in text bubbles. -/
  padding : Nat := Tree.padding
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
  bgOpacity : Float := 0.1
  /-- The default rounding of the background rectangle. -/
  bgRounding : Nat := 10
  /-- The highlight stroke width of the background rectangle border. -/
  bgStrokeWidth : Nat := 3
  /-- The highlight color of the background rectangle border. -/
  bgStrokeColor : Svg.Color := (0.2, 0.6, 1.0)

private structure TreeRenderParams extends TextBubbleParams, BackgroundFrameParams where
  /-- The number of pixels occupied by each row in the tree display. -/
  rowHeight : Nat := Tree.rowSize
  /-- The list of selected locations in the rendered proof state. -/
  selectedLocations : Array SubExpr.Pos
  /-- The current frame in the SVG. -/
  frame : Svg.Frame
  /-- The color of the current frame. -/
  color : Svg.Color := bgColor
  /-- The polarity of the current sub-expression, which indicates whether it is in positive or negative position. -/
  polarity : Bool := true
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

/-- Change to the opposite polarity. -/
def withOppositePolarity : TreeRenderM α → TreeRenderM α :=
  withReader (polarity %~ Bool.not)

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
    ( { f with height := height }, 
      { f with ymin := f.ymin + size, height := f.height - height } )

/-- Work on the top row of the current frame and specify what to do on the rest. -/
abbrev withTopRowSplit (rowAct : TreeRenderM Unit) (restAct : TreeRenderM Unit) : TreeRenderM Unit := do
  withVerticalSplit (← read).rowHeight rowAct restAct

/-- Checks if the current position is selected. -/
def isSelected : TreeRenderM Bool := do
  let ρ ← read
  return ρ.selectedLocations.contains ρ.pos

partial def Html.toString : Html → String
  | .element tag attrs children => s!"Element {tag} {attrs} {children.map toString}"
  | .text t => s!"Text {t}"
  | .component _ name _ children => s!"Component {name} {children.map toString}"

instance : ToString Html where
  toString := Html.toString

structure InteractiveRectangleProps where
  width : Nat
  height : Nat
  color : String
  borderRadius : Nat := 10
  loc : SubExpr.Pos
  opacity : Float := 0.4
  borderWidth : Nat := 3
  highlightColor : String := "blue"
deriving Server.RpcEncodable

@[widget_module]
def InteractiveRectangle : Component InteractiveRectangleProps where
  javascript := include_str "../../build/js/interactiveRectangle.js"

open scoped Jsx in
/-- Draw a rectangle bounding the current frame, set to highlight when 
    the current position is selected in the UI. -/
def drawFrame : TreeRenderM Unit := do
  let ρ ← read
  draw <| .element "foreignObject" #[
      ("x", toJson ρ.frame.xmin),
      ("y", toJson ρ.frame.ymin),
      ("width", toJson ρ.frame.width),
      ("height", toJson ρ.frame.height)
    ] #[<InteractiveRectangle
          width={ρ.frame.width}
          height={ρ.frame.height}
          color={ρ.color.toStringRGB}
          loc={ρ.pos}
          opacity={ρ.bgOpacity}
          borderRadius={ρ.bgRounding}
          borderWidth={ρ.bgStrokeWidth}
          highlightColor={ρ.bgStrokeColor.toStringRGB} />]

open scoped Jsx in
/-- Draw a piece of interactive code at the center of the current frame. -/
def drawCode (code : CodeWithInfos) (color : Svg.Color) : TreeRenderM Unit := do
  let ρ ← read
  let codeLength := ρ.charWidth * code.pretty.length
  let (x, y) := (ρ.frame.xmin + (ρ.frame.width / 2 - ρ.padding - codeLength / 2).toFloat * ρ.frame.pixelSize, 
                 ρ.frame.ymin + (ρ.frame.height / 2 - ρ.height / 2).toFloat * ρ.frame.pixelSize)
  draw <| .element "rect" #[
    ("x", toJson x),
    ("y", toJson y),
    ("width", toJson <| codeLength.toFloat + 2 * ρ.padding.toFloat * ρ.frame.pixelSize),
    ("height", ρ.height),
    ("rx", ρ.rounding),
    ("fill", color.toStringRGB),
    ("opacity", toJson ρ.opacity)
  ] #[]
  draw <| .element "foreignObject" #[
    ("x", toJson <| x + ρ.padding.toFloat * ρ.frame.pixelSize),
    ("y", toJson y),
    ("width", codeLength),
    ("height", ρ.height)
  ] #[< InteractiveCode fmt={code} />]

end TreeRender

open TreeRender in
/--

Render a `DisplayTree` as an SVG image within the `TreeRenderM` monad.

# TO-DO:
- Coloring based on polarity

-/
def Tree.DisplayTree.renderCore (displayTree : Tree.DisplayTree) : TreeRenderM Unit := do
  let ρ ← read
  drawFrame
  match displayTree with
  | .forall quantifier name type body =>
    withTopRowSplit
      (drawCode (.append #[quantifier, name, .text " : ", type]) ρ.forallQuantifierColor)
      (descend 1 <| renderCore body) 
  | .exists quantifier name type body =>
    withTopRowSplit
      (drawCode (.append #[quantifier, name, .text " : ", type]) ρ.existsQuantifierColor)
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
      withHorizontalSplit ((ρ.frame.width - ρ.rowHeight) / 2)
        (descend 0 <| withColor ρ.conjunctionColor <| renderCore first)
        (withHorizontalSplit ρ.rowHeight
          (drawCode wedge ρ.conjunctionColor)
          (descend 1 <| withColor ρ.conjunctionColor <| renderCore second))
  | .not neg body =>
    withHorizontalSplit ρ.rowHeight
      (drawCode neg ρ.negationColor)
      (descend 1 <| withColor ρ.negationColor <| renderCore body)
  | .node val => 
    withTopRowSplit
      (descend 2 <| drawCode val ρ.nodeColor)
      (pure ())

section Rendering

deriving instance TypeName for Tree.DisplayTree

structure GoalSelectionProps where
  pos : Lsp.Position
  tree : WithRpcRef Tree.DisplayTree
  locations : Array SubExpr.Pos
deriving RpcEncodable

open scoped Jsx in
@[server_rpc_method]
def renderTree (props : GoalSelectionProps) : RequestM (RequestTask Html) := RequestM.asTask do
  let tree := props.tree.val
  let yScale := Tree.rowSize
  let width := tree.width
  let height := tree.depth * yScale
  let frame : Svg.Frame := { xmin := 0, ymin := 0, xSize := width.toFloat, width := width, height := height }
  let (_, ⟨elements⟩) := tree.renderCore |>.run {} |>.run { selectedLocations := props.locations, frame := frame }
  return (
    <div align="center">
      {.element "svg"
      #[("xmlns", "http://www.w3.org/2000/svg"),
        ("version", "1.1"),
        ("width", width),
        ("height", height)]
      elements}
      <hr />
      -- {.element "div" #[] (props.locations.map (<p>{.text ·.toString}</p>))}
    </ div>
    )

@[widget_module]
def RenderTree : Component GoalSelectionProps where
  javascript := include_str "../../build/js/svgTreeTest.js"

open Elab Tactic Json in
elab stx:"display_tree" : tactic => do
  let e ← getMainTarget
  let (t, _) ← Tree.toDisplayTree 
            |>.run { optionsPerPos := ∅, currNamespace := (← getCurrNamespace), openDecls := (← getOpenDecls), subExpr := ⟨e, .root⟩ }
            |>.run {}
  Widget.savePanelWidgetInfo (hash RenderTree.javascript) (stx := stx) do
    return json% { tree : $(← rpcEncode (WithRpcRef.mk t) ), locations : $( (.empty : Array SubExpr.Pos) )} 

example : ∀ x : Nat, True ∧ False → ¬ True := by
  make_tree
  display_tree
  sorry

end Rendering