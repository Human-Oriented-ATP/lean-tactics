import Lean.Server.Rpc.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay

namespace ProofWidgets
open Lean Server Elab

structure DynamicButtonProps where
  label : String
  html : Html

#mkrpcenc DynamicButtonProps

@[widget_module] def DynamicButton : Component DynamicButtonProps where
  javascript := include_str "../build/js/dynamicButton.js"

open scoped Jsx in
#html <DynamicButton label={"Hello"} html={<b>World</b>} />