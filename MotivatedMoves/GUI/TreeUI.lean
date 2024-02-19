import ProofWidgets

open Lean Widget ProofWidgets Server

structure Svg.TreeNode (f : Svg.Frame) where
  point : Svg.Point f
  expr : CodeWithInfos
  color : Svg.Color
  selectable : Bool := true
  opacity : Float := 1.0
  highlight : Bool := false

open scoped Jsx in
def Svg.TreeNode.toHtml {f : Svg.Frame} (node : TreeNode f) : Array Html :=
  let length := node.expr.pretty.length
  let (x, y) := node.point.toAbsolute
  let charWidth := 8 -- the approximate width of a Unicode character in pixels
  let padding := 4
  let boundary := Html.element "rect" #[
    ("x", toJson x),
    ("y", toJson y),
    ("width", toJson (charWidth * length + 2*padding)),
    ("height", 20),
    ("rx", 10),
    ("opacity", toJson node.opacity),
    ("fill", node.color.toStringRGB)
    ] #[]
  let text := Html.element "foreignObject" #[
    ("x", toJson (x + padding.toFloat)),
    ("y", toJson y),
    ("width", toJson (charWidth * length)),
    ("height", 20)
  -- ] #[<p style={json% {"font-family":"JetBrains Mono"}}>{.text node.expr.pretty}</p>]
  ] #[<InteractiveCode fmt={node.expr} />]
  #[boundary, text]

structure GoalSelectionProps where
  pos : Lsp.Position
  expr : CodeWithInfos
  locations : Array SubExpr.Pos

#mkrpcenc GoalSelectionProps

open Meta Elab Term Jsx Json

#eval (SubExpr.Pos.root.toString)

@[server_rpc_method]
def GoalRendering.rpc (props : GoalSelectionProps) : RequestM (RequestTask Html) := RequestM.asTask do
  let length := props.expr.pretty.length
  let charWidth := 8 -- the approximate width of a Unicode character in pixels
  let padding := 4
  let (x, y) := (100, 200)
  let boundary := Html.element "rect" (#[
    ("x", toJson 100),
    ("y", toJson 200),
    ("width", toJson (charWidth * length + 2*padding)),
    ("height", 20),
    ("rx", 10),
    ("opacity", toJson 0.7),
    ("fill", "orange")
    ] |>.append (if (props.locations.contains .root) then #[("stroke-width", 5), ("stroke", "blue")] else #[])) #[]
  let text := Html.element "foreignObject" #[
    ("x", toJson (x + padding.toFloat)),
    ("y", toJson y),
    ("width", toJson (charWidth * length)),
    ("height", 20)
  ] #[<InteractiveCode fmt={props.expr} />]
  return .element "svg"
    #[("xmlns", "http://www.w3.org/2000/svg"),
      ("version", "1.1"),
      ("width", 500),
      ("height", 500)]
    #[boundary, text]

open Jsx Json

@[server_rpc_method]
def Panel.rpc (props : GoalSelectionProps) : RequestM (RequestTask Html) := RequestM.asTask do
  return .element "div" #[] <| props.locations.map fun loc ↦ <p> {.text s!"Selected {loc.toString}\n"} </p>

@[widget_module]
def SvgHighlight : Component GoalSelectionProps where
  javascript := include_str "../../build/js/svgClickHighlight.js"

open Lean Elab Command Term in
elab stx:"#draw" t:term : command =>
  runTermElabM fun _ ↦ do 
    let e ← Term.elabTerm t none
    let infos ← Widget.ppExprTagged e
    Widget.savePanelWidgetInfo (hash SvgHighlight.javascript) (stx := stx) do
      return json% { expr: $(← rpcEncode infos), locations: $( (.empty : Array SubExpr.Pos)) }

#draw 1 + 1
