import ProofWidgets.Component.OfRpcMethod

open Lean Server ProofWidgets

structure Reducer (σ α : Type _) [RpcEncodable σ] [RpcEncodable α] where
  init : σ
  update : σ → α → σ
  html : σ → RequestM (RequestTask Html)

namespace Reducer

variable {σ α : Type _} [RpcEncodable σ] [RpcEncodable α]

def mkRef (ρ : Reducer σ α) : BaseIO (IO.Ref (σ × Array α)) := 
  IO.mkRef (ρ.init, #[])

-- IDEA: Define a `ReducerM` reader monad over IO/RequestM
-- that includes the `Reducer` and `Ref` information

def updateRef (ρ : Reducer σ α) (ref : IO.Ref (σ × Array α)) (a : α) : IO Unit := do
  let (state, actions) ← ref.get
  ref.set (ρ.update state a, actions.push a)

def getHtml (ρ : Reducer σ α) (ref : IO.Ref (σ × Array α)) : RequestM (RequestTask Html) := do
  let (s, _) ← ref.get
  ρ.html s

def registerRequest (ρ : Reducer σ α) (ref : IO.Ref (σ × Array α)) (a : α) : 
    RequestM (RequestTask Html) := do
  ρ.updateRef ref a
  ρ.getHtml ref

end Reducer


section Test

structure LspButtonProps where
  label : String
deriving ToJson, FromJson

@[widget_module]
def LspButton : Component LspButtonProps where
  javascript := include_str "../build/js/lspTestButton.js"

structure TestParams where
  position : Lsp.Position
deriving ToJson, FromJson

open scoped Jsx in
def testReducer : Reducer Nat TestParams := {
  init := 0,
  update := fun n _ ↦ n + 1,
  html := fun n ↦
    return .pure <LspButton label={s!"Clicked {n} times"} />
}

initialize testReducerRef : IO.Ref (Nat × Array TestParams) ← testReducer.mkRef

@[server_rpc_method]
def registerTestReq := testReducer.registerRequest testReducerRef

end Test