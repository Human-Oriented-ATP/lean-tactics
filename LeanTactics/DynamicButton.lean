import Lean.Server.Rpc.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay

namespace ProofWidgets
open Lean Server Elab

structure DynamicButtonProps where
  label : String
  edit : Lsp.TextDocumentEdit
  newCursorPos? : Option Lsp.Position := none
  html : Option Html := none

#mkrpcenc DynamicButtonProps

@[widget_module] def DynamicButton : Component DynamicButtonProps where
  javascript := include_str "../build/js/dynamicButton.js"