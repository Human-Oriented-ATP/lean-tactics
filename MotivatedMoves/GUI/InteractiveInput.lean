import Lean
import Mathlib.Tactic
import ProofWidgets

open Lean Server ProofWidgets Json Jsx

initialize formRef : IO.Ref Json ← IO.mkRef .null

structure NoProps where
deriving ToJson, FromJson

deriving instance RpcEncodable for PUnit

@[server_rpc_method]
def Form.rpc (props : Json) : RequestM (RequestTask Unit) := RequestM.asTask do
  formRef.set props

@[widget_module] def Form : Component NoProps where
  javascript := include_str "../../build/js/interactiveInput.js"