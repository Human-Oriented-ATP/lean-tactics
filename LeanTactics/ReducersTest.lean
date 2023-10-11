import LeanTactics.Reducers
import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets Server Html Jsx

-- structure HtmlReducerRenderingProps where
--   html : Html
-- deriving Server.RpcEncodable

-- @[widget_module]
-- def HtmlReducerRendering : Component HtmlReducerRenderingProps where
--   javascript := include_str "../build/js/reducerRendering.js"

#html .ofComponent HtmlReducerRendering ⟨<p> Hello World </p>⟩ #[]