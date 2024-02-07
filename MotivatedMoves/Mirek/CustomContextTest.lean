import Lean
import ProofWidgets

open Lean Server ProofWidgets Jsx Json

def customContextTestCode :=
  "
  import * as React from 'react';
  import { jsxs, jsx } from 'react/jsx-runtime';

  export const CustomContext = React.createContext(0)

  export function ComponentA() {
      let ctx = React.useContext(CustomContext);
      return React.createElement('p', null, `Component A with context value ${ctx}.`)
  }

  export function ComponentB() {
      let ctx = React.useContext(CustomContext);
      return React.createElement('p', null, `Component B with context value ${ctx}.`)
  }

  export function CombinedComponentTest(props) {
      return React.createElement('CustomContext.Provider', { value : 5 }, ...props.children);
  }"

structure NoProps where
deriving ToJson, FromJson

@[widget_module]
def ComponentA : Component NoProps where
  javascript := customContextTestCode
  «export» := "ComponentA"

@[widget_module]
def ComponentB : Component NoProps where
  javascript := customContextTestCode
  «export» := "ComponentB"

@[widget_module]
def CombinedComponentTest : Component NoProps where
  javascript := customContextTestCode
  «export» := "CombinedComponentTest"

#html
  <CombinedComponentTest>
    <ComponentA />
    <ComponentB />
  </CombinedComponentTest>

def customContextTestCode2 :=
  "
  import { jsxs, jsx } from 'react/jsx-runtime';
  import * as React from 'react';
  const ctx = React.createContext(0);
  export function ComponentA(){
    let ctxVal = React.useContext(ctx);
    return jsxs('p',{children:
      ['Component A with context value ',ctxVal,'.']
    })
  }
  export function ComponentB(){
    let ctxVal = React.useContext(ctx);
    return jsxs('p',{children:
      ['Component B with context value ',ctxVal,'.']
    })
  }
  function CombinedComponentTest(props){
    return jsxs(ctx.Provider,{value:props.value,children:props.children})
  }
  export{CombinedComponentTest as default};"

structure CtxProps where
  value : Int
deriving FromJson, ToJson

@[widget_module]
def CombinedComponentTest2 : Component CtxProps where
  javascript := customContextTestCode2

@[widget_module]
def ComponentA2 : Component NoProps where
  javascript := customContextTestCode2
  «export» := "ComponentA"

@[widget_module]
def ComponentB2 : Component NoProps where
  javascript := customContextTestCode2
  «export» := "ComponentB"

#html
  <CombinedComponentTest2 value={42}>
    <ComponentA2/>
    <ComponentB2/>
  </CombinedComponentTest2>
