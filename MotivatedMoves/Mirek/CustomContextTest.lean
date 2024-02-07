import Lean
import ProofWidgets

open Lean Server ProofWidgets Jsx Json

def customContextTestCode := 
  "import * as React from 'react';

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

-- def customContextTestCode := include_str "../../build/js/customContextTest.js"

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