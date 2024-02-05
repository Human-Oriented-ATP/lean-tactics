import Lean
import ProofWidgets

open Lean ProofWidgets Server

initialize testRef : IO.Ref Nat ← IO.mkRef 0

structure NoProps where
deriving ToJson, FromJson

@[server_rpc_method]
def incrementRef (_props : NoProps) : RequestM (RequestTask NoProps) := do
  RequestM.asTask do
    let val ← testRef.get
    testRef.set val.succ
    return {}

@[widget_module]
def TestRef : Component NoProps where
  javascript :=
"
import { RpcContext, mapRpcError } from '@leanprover/infoview'
import * as React from 'react';
const e = React.createElement;

export default function(props) {
  const rs = React.useContext(RpcContext);

  return e('button', { onClick: () => {
    rs.call('incrementRef', props)
      .catch(e => { console.log(mapRpcError(e).message) })
    }}, 'Increment counter')
}
"
