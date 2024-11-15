import ProofWidgets
open ProofWidgets.Jsx

-- varValues: values of individual free variables
-- bounds: sorted list of bounds by the model value,
--   grouped together if they are the same
-- counts: an array one smaller than bounds,
--   telling how many items there are between the bounds
structure WindowModel where
  varValues : List (String × Int)
  bounds : List (Int × List String)
  blocks : List (Nat × Nat)
deriving Lean.Server.RpcEncodable

def List.interleave (l1 : List α) : List α → List α
| [] => l1
| l2@(h2::t2) => match l1 with
  | [] => l2
  | h1::t1 => h1::h2::(List.interleave t1 t2)

namespace WindowModel

def toString (m : WindowModel) : Lean.Meta.MetaM String
:= do
  let vvLines : List String ← m.varValues.mapM (
    fun (e, value) => do
    -- let eStr ← Lean.Meta.ppExpr e
    return s!"  {e} = {value}"
  )
  let boundLines ← m.bounds.mapM (
    fun (val, bs) => do
    -- let bs ← bs.mapM Lean.Meta.ppExpr
    let bs := bs.map ToString.toString
    return "  " ++ (val.repr) ++ " = " ++ (" = ".intercalate bs)
  )
  let mut blockLines := m.blocks.map (
    fun (count, size) => s!"  : {count} / {size}"
  )
  let lines := ["Model"] ++ vvLines ++ [""] ++ (boundLines.interleave blockLines)
  return ("\n".intercalate lines)


def exampl : WindowModel
:= {
  varValues := []
  bounds := [
    (-1, ["n^2-10", "k^0-2"]),
    (3, ["n"]),
    (5, ["n*2-1", "n+k-1"]),
    (6, ["n*2", "n+k"]),
    (10, []),
    (15, ["k"])
  ]
  blocks := [(2,4), (0,2), (0,1), (4,4), (2,5)]
}

def cellSize : Nat := 20
def maxLabelCell : Nat := 6 -- in half-cells taken on both sizes

def mainRowHtml (wm : WindowModel) : ProofWidgets.Html
:= Id.run do
  let mut cells : Array ProofWidgets.Html := #[]
  -- match wm.blocks.head? with
  -- | some (_,size) =>
  --   let size := halfCellSize*(min size maxLabelCell)
  --   cells := cells.push <td width={size} colspan={2}></td>
  -- | none => pure ()
  for (count, size) in wm.blocks do
    let leftBorders := #[3] ++ (Array.mkArray (size-1) 1)
    let rightBorders := (Array.mkArray (size-1) 1).push 3
    let contents := (Array.mkArray count "●︎").append (Array.mkArray (size-count) "")
    let fadeds :=
      if count >= size then
        (Array.mkArray size false)
      else
        (Array.mkArray count true).append (Array.mkArray (size-count) true)
    for (leftBorder, rightBorder, content, faded) in leftBorders.zip (rightBorders.zip (contents.zip fadeds)) do
      let mut styleList : List (String × Lean.Json) :=
        [
          ("text-align", "center"),
          ("min-width", s!"{cellSize}px"),
          ("border-left", s!"{leftBorder}px solid white"),
          ("border-top", "1px solid white"),
          ("border-bottom", "1px solid white"),
          ("border-right", s!"{rightBorder}px solid white")
        ]
      if faded then styleList := ("color", "gray")::styleList
      let style : Lean.Json := .mkObj styleList
      cells := cells.push <td style={style}>{.text content}</td>

  -- match wm.blocks.getLast? with
  -- | some (_,size) =>
  --   let size := halfCellSize*(min size maxLabelCell)
  --   cells := cells.push <td width={size} colspan={2}></td>
  -- | none => pure ()
  return .element "tr" #[] cells

def labelRowHtml (wm : WindowModel) (labels : List ProofWidgets.Html) : ProofWidgets.Html
:= Id.run do
  let mut cells : Array ProofWidgets.Html := #[]
  -- let mut prevLabelSize : Option Nat := none
  let sizes := wm.blocks.map Prod.snd
  for (label,(size : Nat)) in labels.zip (sizes++[1]) do
  -- for (label,left,right) in labels.zip (([0]++sizes).zip (sizes++[0])) do
  --   let leftSize := if left == 0 then maxLabelCell else left
  --   let rightSize := if right == 0 then maxLabelCell else right
  --   let labelSize := min (min leftSize rightSize) maxLabelCell
  --   match prevLabelSize with
  --   | some s =>
  --     let spaceSize := 2*leftSize - s - labelSize
  --     if spaceSize > 0 then
  --       cells := cells.push <td colspan={spaceSize}></td>
  --   | none => pure ()
  --   prevLabelSize := some labelSize
  --   let leftSpan := if left == 0 then 2 else labelSize
  --   let rightSpan := if right == 0 then 2 else labelSize
  --   let labelSpan := leftSpan + rightSpan
    cells := cells.push
      <td
        colspan={size}
        style={json% {
          -- border: "1px solid blue",
          -- "text-align": "center",
          "padding-right": "5px"
        }}
      >{label}</td>
  return .element "tr" #[] cells

#check List.maximum?

def tableHtml (wm : WindowModel) : ProofWidgets.Html
:= Id.run do
  let mut rows := #[]
  let labelNums := wm.bounds.map (fun (_,labels) => labels.length)
  let maxLabelNum := match labelNums.maximum? with | some x => x | none => 0
  rows := rows.push (wm.labelRowHtml (wm.bounds.map (fun (val,_) => .text (ToString.toString val))))
  rows := rows.push wm.mainRowHtml
  for i in List.range maxLabelNum do
    rows := rows.push (wm.labelRowHtml (
      wm.bounds.map (
        fun (_,labels) =>
        match labels.get? i with
        | some label => .text label
        | none => .text ""
      )
    ))
  return .element "table" #[("style", json% {"border-collapse": "collapse" })] rows

def varValuesHtml (wm : WindowModel) : ProofWidgets.Html
:=
  let elements : List ProofWidgets.Html := wm.varValues.bind (
    fun (var, val) =>
    [.text s!"{var} = {val}", <br/>]
  )
  .element "p" #[] elements.toArray

def toHtml (wm : WindowModel) : ProofWidgets.Html
:= <div>
  {wm.varValuesHtml}
  {wm.tableHtml}
</div>

#html exampl.toHtml

open Lean.Server in
@[server_rpc_method]
private def rpc (wm : WindowModel) : Lean.Server.RequestM (Lean.Server.RequestTask ProofWidgets.Html)
:= RequestM.asTask do return wm.toHtml

@[widget_module]
def Component : ProofWidgets.Component WindowModel :=
  mk_rpc_widget% rpc

def showHtml (wm : WindowModel) (stx : Lean.Syntax) : Lean.Core.CoreM Unit :=
  Lean.Widget.savePanelWidgetInfo Component.javascriptHash
    (Lean.Server.rpcEncode wm) stx

end WindowModel
