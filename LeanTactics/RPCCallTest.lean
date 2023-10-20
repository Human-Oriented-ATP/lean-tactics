import Lean
import ProofWidgets.Component.HtmlDisplay

open Lean Server ProofWidgets

structure TestProps where
  n : Nat
deriving ToJson, FromJson

@[server_rpc_method]
def testRpcMethod (props : TestProps) : RequestM (RequestTask Nat) := do
  IO.sleep 1000
  return .pure (props.n + 10)

@[widget_module]
def TestRpcCall : Component TestProps where
  javascript := "
import * as React from 'react'
import { RpcContext, mapRpcError, useAsyncPersistent } from '@leanprover/infoview'

export default function TestRpcCall(props) {
  const e = React.createElement
  const rs = React.useContext(RpcContext)
  const st = useAsyncPersistent(async () => {
    return await rs.call('testRpcMethod', props);
  }, [rs, props])
  return st.state === 'rejected' ?
      e('p', {style : {color: 'red'}}, mapRpcError(st.error).message)
    : st.state === 'loading' ?
      e(React.Fragment, null, 'Loading...')
    :
      e('p', null, 'Received ', st.value, '.')
}
"

open scoped Jsx in
#html <TestRpcCall n={10} />
