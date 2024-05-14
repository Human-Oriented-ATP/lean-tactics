import * as React from 'react';
import { LocationsContext, SubexprPos, GoalsLocation } from '@leanprover/infoview';

interface InteractiveRectangleProps {
    width : number
    height : number
    borderRadius : number
    color : string
    loc: SubexprPos
    opacity: number
    borderWidth : number
    highlightColor : string 
}

export default function Rectangle(props:InteractiveRectangleProps) : JSX.Element {
    const [opacity, setOpacity] = React.useState(props.opacity);
    const locs = React.useContext(LocationsContext)
    const currentLoc : GoalsLocation = { mvarId: '', loc : { target : props.loc } }
    return (
    <div id="rectangle" 
        style={{ 
            width: props.width, 
            height: props.height, 
            background: props.color,
            borderRadius: props.borderRadius,
            opacity: opacity, 
            borderWidth: props.borderWidth, 
            borderColor: locs?.isSelected(currentLoc) ? props.highlightColor : "transparent",
            borderStyle: "outset" }}
        onMouseOver={() => { setOpacity(1.0) }}
        onMouseOut={() => { setOpacity(props.opacity) }}
        onClick={(e) => { if (e.shiftKey) { locs?.setSelected(currentLoc, on => !on) } }} />
    );
}