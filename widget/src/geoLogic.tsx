import { RpcContext } from '@leanprover/infoview';
import React, { useRef, useEffect } from 'react'
import { Toolbox, ToolName } from './toolbox'
import { GeoViewport } from './geoViewport'
import { GeoStep, GeoModel, runSteps } from './geoConstr'
import * as G from './geoObject'

const points : G.Point[] = [
  [0,1],
  [-1,-1],
  [1,0]
]

const lines : G.Line[] = [
  G.linePP(points[0], points[1]),
  G.linePP(points[1], points[2]),
  G.linePP(points[2], points[0]),
]

const circles : G.Circle[] = [
  G.circumcircle(points[0], points[1], points[2]),
]

function GeoLogic(props : {}) {
  const rs = React.useContext(RpcContext)
  const [tool,setTool] = React.useState<ToolName>('point')
  const [constr,setConstrState] = React.useState<GeoStep[]>([])
  const [model,setModel] = React.useState<GeoModel>({
    points:[],
    lines:[],
    circles:[],
  })
  const cancelCallback = React.useRef<null | {() : boolean}>(null)

  async function setConstr(constr : GeoStep[]) {
    const renderLean = true
    var model2 : GeoModel
    if (renderLean)
      model2 = await rs.call<GeoStep[], GeoModel>(
        'GeoLogic.runStepsRPC',
        constr
      )
    else
      model2 = runSteps(constr)
    setConstrState(constr)
    setModel(model2)
  }

  function onKeyDown(e : React.KeyboardEvent){
    const keyToTool : Record<string,ToolName> = {
      x:'point',
      p:'point',
      l:'line',
      t:'perpline',
      c:'circle',
      o:'circumcircle',
      m:'move',
      h:'hide',
      a:'label',
      r:'derive',
    }
    if (e.key in keyToTool) setTool(keyToTool[e.key])
    else if (e.key == 'Backspace') {
      var captured = false
      if (cancelCallback.current !== null)
        captured = cancelCallback.current()
      if (!captured) setConstr(constr.slice(0,-1))
    }
  }

  return <div
    tabIndex={-1}
    onKeyDown={onKeyDown}
    style={{outline:'none'}}
  >
    <Toolbox selected={tool} selectTool={setTool} />
    <GeoViewport tool={tool} constr={constr} model={model}
      setConstr={setConstr}
      registerCancelCallback={(f) => {cancelCallback.current = f}}
    />
  </div>
}

export default GeoLogic
