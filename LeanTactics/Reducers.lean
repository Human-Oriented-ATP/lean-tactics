import ProofWidgets.Component.OfRpcMethod

open Lean Server ProofWidgets

structure Reducer (σ α : Type _) [RpcEncodable σ] [RpcEncodable α] where
  init : σ
  update : σ → α → σ
  html : σ → Html

namespace Reducer

variable {σ α : Type _} [RpcEncodable σ] [RpcEncodable α]
          (ρ : Reducer σ α) (ref : IO.Ref (σ × Array α))

def mkRef : BaseIO (IO.Ref (σ × Array α)) := 
  IO.mkRef (ρ.init, #[])

-- IDEA: Define a `ReducerM` reader monad over IO/RequestM
-- that includes the `Reducer` and `Ref` information

def updateRef (a : α) : IO Unit := do
  let (state, actions) ← ref.get
  ref.set (ρ.update state a, actions.push a)

def getRefHtml : IO Html := do
  let (s, _) ← ref.get
  return ρ.html s

def registerRefRequest (a : α) : RequestM (RequestTask Html) := do
  ρ.updateRef ref a
  return .pure <| ← ρ.getRefHtml ref

end Reducer

structure HtmlReducerRenderingProps where
  html : Html
deriving RpcEncodable

@[widget_module]
def HtmlReducerRendering : Component HtmlReducerRenderingProps where
  javascript := include_str "../build/js/reducerRendering.js"


section Test

structure LspButtonProps where
  label : String
  method : String
deriving ToJson, FromJson

@[widget_module]
def LspButton : Component LspButtonProps where
  javascript := include_str "../build/js/lspTestButton.js"

open scoped Jsx in
def testReducer : Reducer Nat LspButtonProps where
  init := 0
  update := fun n _ ↦ n + 1
  html := fun n ↦
    <LspButton label={s!"Clicked {n} times"} method={"testReducer.registerRequest"} />

initialize testReducer.Ref : IO.Ref (Nat × Array LspButtonProps) ← testReducer.mkRef

@[server_rpc_method]
def testReducer.registerRequest (a : LspButtonProps) : RequestM (RequestTask Html) := do
  IO.FS.writeFile "./rpc_call_test.txt" (toString <| toJson a)
  testReducer.registerRefRequest testReducer.Ref a

end Test