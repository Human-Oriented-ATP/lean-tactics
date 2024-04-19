import Lean
import ProofWidgets

open Lean Server ProofWidgets Jsx

structure InteractiveMessageDataProps where
  msg : WithRpcRef MessageData
deriving RpcEncodable

@[widget_module]
def InteractiveMessageData : Component InteractiveMessageDataProps where
  javascript := 
   "import * as React from 'react';
    import { InteractiveMessageData } from '@leanprover/infoview';

    export default InteractiveMessageData;"

def testMsg : MessageData := m!"Hello"

#html <InteractiveMessageData msg={.mk testMsg} />