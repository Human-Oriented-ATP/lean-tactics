import LeanTactics.Reducers
import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets Server Html Jsx Json

elab "#test_reducer" : command => do
  let (σ, _) ← testReducer.Ref.get
  let code := testReducer.html σ
  Elab.Command.runTermElabM fun _ ↦ do 
    savePanelWidgetInfo (← getRef) ``HtmlReducerRendering do
      return json% { html : $(← rpcEncode code)}

#test_reducer

#eval show IO _ from do
    let (s, _) ← testReducer.Ref.get
    return s 

structure JsonProps where
  json : Json

instance : FromJson JsonProps where
  fromJson? j := return ⟨j⟩

instance : ToJson JsonProps where
  toJson := JsonProps.json

@[server_rpc_method]
def testRpcMethod (props : JsonProps) : RequestM (RequestTask Html) := do
  IO.FS.writeFile "./test_lsp_button.txt" (toString <| toJson props)
  -- let _ : LspButtonProps ← fromJson? props.json
  return .pure <p>Success</p>

#html <LspButton label={"Test Lsp button"} method={"testRpcMethod"} />