import React, { useRef, useEffect, createContext } from 'react'
import SvgPoint from './icons/point'
import SvgLine from './icons/line'
import SvgPerpline from './icons/perpline'
import SvgCircle from './icons/circle'
import SvgCircumcircle from './icons/circumcircle'
import SvgMove from './icons/move'
import SvgHide from './icons/hide'
import SvgLabel from './icons/label'
import SvgDerive from './icons/derive'

export type ToolName = 'point' | 'line' | 'perpline' | 'circle' | 'circumcircle' | 'move' | 'hide' | 'label' | 'derive'

const toolIcons : Record<ToolName, JSX.Element> = {
  point: <SvgPoint />,
  line: <SvgLine />,
  perpline: <SvgPerpline />,
  circle: <SvgCircle />,
  circumcircle: <SvgCircumcircle />,
  move: <SvgMove />,
  hide: <SvgHide />,
  label: <SvgLabel />,
  derive: <SvgDerive />,
}

interface ToolButtonProps {
  label : ToolName
  isSelected : boolean
  setSelected () : void
  icon : JSX.Element
}
interface ToolboxProps {
  selected : ToolName
  selectTool (label: ToolName) : void
}

function ToolboxButton(props : ToolButtonProps)
{
  const style = props.isSelected ? {backgroundColor: "darkGrey"} : {}

  return <button
    onClick={() => {
      if (!props.isSelected)
        return props.setSelected()
    }}
    style={style}
  >
    {props.icon}
  </button>
}

export function Toolbox(props : ToolboxProps) {
  const firstTool : ToolName = 'point'

  return <div>
    {(Object.entries(toolIcons) as [ToolName,JSX.Element][]).map((
      [label,icon]) =>
      <ToolboxButton
        label={label}
        icon={icon}
        isSelected={label == props.selected}
        setSelected={() => { props.selectTool(label) }} />
    )}
  </div>
}
