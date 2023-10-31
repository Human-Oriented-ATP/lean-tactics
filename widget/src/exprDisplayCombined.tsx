import * as React from 'react'
import {LocationsContext, InteractiveCode, TaggedText, GoalsLocation, SubexprInfo, DocumentPosition, SubexprPos } from '@leanprover/infoview';

export interface ExprSelectionProps {
  pos: DocumentPosition
  expr: TaggedText<SubexprInfo>
  subexprPos: string
}

export interface ExprDisplayProps extends ExprSelectionProps {
  description : string
}

export default function(props:{exprs : ExprDisplayProps[]}) {
    const [selectedLocs, setSelectedLocs] = React.useState<GoalsLocation[]>([]);
    const locs = (pos:SubexprPos) => React.useMemo(() => ({
        isSelected: (l : GoalsLocation) => selectedLocs.some(v => GoalsLocation.isEqual(v, l)),
        setSelected: (l : GoalsLocation, act : any) => setSelectedLocs(ls => {
            // We ensure that `selectedLocs` maintains its reference identity if the selection
            // status of `l` didn't change.
            const newLocs = ls.filter(v => !GoalsLocation.isEqual(v, l));
            const wasSelected = newLocs.length !== ls.length;
            const isSelected = typeof act === 'function' ? act(wasSelected) : act;
            if (isSelected)
                newLocs.push(GoalsLocation.withSubexprPos(l, pos));
            return wasSelected === isSelected ? ls : newLocs;
        }),
        subexprTemplate: { mvarId: '', loc: { target: pos }}
    }), [selectedLocs]);
    return (
    <div>
        { props.exprs.map((prop:ExprDisplayProps) =>
        <div>
            <p>{prop.description}</p>
            <LocationsContext.Provider value={locs(prop.subexprPos)}>
                {InteractiveCode({fmt : prop.expr})}
            </LocationsContext.Provider>
        </div>
        ) }
        <hr />
        {
        <div>
            { selectedLocs.map((loc:GoalsLocation) => 
                ('target' in loc.loc) ? 
                <p>Selected {loc.loc.target}</p> : 
                <p></p>) }
        </div>
        }
    </div>
    );
}
