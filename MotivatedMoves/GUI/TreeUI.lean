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
  let boundary := Html.element "rect" #[
    ("x", toJson x),
    ("y", toJson y),
    ("width", toJson (charWidth * length)),
    ("height", 40),
    ("rx", 10),
    ("opacity", toJson node.opacity),
    ("fill", node.color.toStringRGB)
    ] #[]
  let text := Html.element "foreignObject" #[
    ("x", toJson (x + 1)),
    ("y", toJson y),
    ("width", toJson (charWidth * length)),
    ("height", 30)
  ] #[<p style={json% {"font-family":"JetBrains Mono"}}>{.text node.expr.pretty}</p>]
  #[boundary, text]

def frame : Svg.Frame := {
  xmin := 0, ymin := 0, xSize := 500, width := 500, height := 500
}

def node : Svg.TreeNode frame := {
  point := .px 30 400, expr := .text "Hello World", color := ⟨1.0, 0.6, 0.2⟩, opacity := 0.6
}

open Jsx Json

#html .element "svg"
    #[("xmlns", "http://www.w3.org/2000/svg"),
      ("version", "1.1"),
      ("width", frame.width),
      ("height", frame.height)]
    node.toHtml