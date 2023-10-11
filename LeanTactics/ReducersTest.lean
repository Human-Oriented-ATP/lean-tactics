import LeanTactics.Reducers
import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets Server Html Jsx

structure HtmlReducerRenderingProps where
  html : Html
deriving Server.RpcEncodable

@[widget_module]
def HtmlReducerRendering : Component HtmlReducerRenderingProps where
  javascript := include_str "../build/js/reducerRendering.js"

#eval show IO _ from do
  let (x, y) ← (testReducer.Ref.get : IO _)
  return x

#html .ofComponent HtmlReducerRendering ⟨testReducer.html testReducer.init⟩ #[]