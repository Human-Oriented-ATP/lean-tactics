import LeanTactics.Reducers
import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets Server Html Jsx Json

structure HtmlReducerRenderingProps where
  html : Html
deriving Server.RpcEncodable

@[widget_module]
def HtmlReducerRendering : Component HtmlReducerRenderingProps where
  javascript := include_str "../build/js/reducerRendering.js"

#eval show IO _ from do
  let (x, y) ← (testReducer.Ref.get : IO _)
  return x


elab "#test_reducer" : command => do
  let (σ, _) ← testReducer.Ref.get
  let code := testReducer.html σ
  Elab.Command.runTermElabM fun _ ↦ do 
    savePanelWidgetInfo (← getRef) ``HtmlReducerRendering do
      return json% { html : $(← rpcEncode code)}

#test_reducer