import React, { useState } from 'react';
import {LocationsContext, InteractiveCode, DocumentPosition, TaggedText, GoalsLocation, SubexprInfo } from '@leanprover/infoview';

export interface ExprPresentProps {
    pos : DocumentPosition
    expr : TaggedText<SubexprInfo>
}

const InfoDisplayContent = React.memo((props : ExprPresentProps) => {
    const pos = props.pos
    const [selectedLocs, setSelectedLocs] = React.useState<GoalsLocation[]>([]);
    React.useEffect(() => setSelectedLocs([]), [pos.uri, pos.line, pos.character]);
    const locs = React.useMemo(() => ({
        isSelected: (l : GoalsLocation) => selectedLocs.some(v => GoalsLocation.isEqual(v, l)),
        setSelected: (l : GoalsLocation, act : any) => setSelectedLocs(ls => {
            // We ensure that `selectedLocs` maintains its reference identity if the selection
            // status of `l` didn't change.
            const newLocs = ls.filter(v => !GoalsLocation.isEqual(v, l));
            const wasSelected = newLocs.length !== ls.length;
            const isSelected = typeof act === 'function' ? act(wasSelected) : act;
            if (isSelected)
                newLocs.push(l);
            return wasSelected === isSelected ? ls : newLocs;
        }),
        subexprTemplate: { mvarId: '', loc: { target: '' }}
    }), [selectedLocs]);
    return <div> 
        (<LocationsContext.Provider value = {locs}>
            {InteractiveCode({fmt : props.expr}) }
        </LocationsContext.Provider>)
    </div>

})

export default InfoDisplayContent