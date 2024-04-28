import * as React from 'react';
import { LocationsContext, importWidgetModule, RpcSessionAtPos, RpcContext, useAsyncPersistent, mapRpcError, GoalsLocation, DocumentPosition, CodeWithInfos, SubexprPos, PanelWidgetProps } from '@leanprover/infoview';
import { Html, renderHtml } from "./htmlDisplay";
import { Range } from 'vscode-languageserver-protocol';

interface GoalSelectionProps extends PanelWidgetProps {
    selections : SubexprPos[]
    range: Range
}

function goalsLocationToSubexprPos(loc:GoalsLocation) : SubexprPos | undefined {
    if ('hypType' in loc.loc) {
        return loc.loc.hypType[1];
    } else if ('hypValue' in loc.loc) {
        return loc.loc.hypValue[1];
    } else if ('target' in loc.loc) {
        return loc.loc.target;
    } else {
        return undefined;
    }
}

const dummyMVarId = "dummyMVarId"

const InfoDisplayContent = React.memo((props : GoalSelectionProps) => {
    const rs = React.useContext(RpcContext)
    const pos = props.pos
    const [selectedLocs, setSelectedLocs] = React.useState<GoalsLocation[]>(props.selections?.map (pos => {return {mvarId: dummyMVarId, loc: {target: pos}}}));
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
        subexprTemplate: { mvarId: dummyMVarId, loc: { target: '/' } }
    }), [selectedLocs]);

    const goalState = useAsyncPersistent<JSX.Element>(async () => {
      const goalRpcProps: GoalSelectionProps = {
        ...props,
        selectedLocations: [],
        selections: selectedLocs.map(goalsLocationToSubexprPos).filter((p: SubexprPos | undefined) : p is SubexprPos => !!p) }
      const html: Html = await rs.call('renderTree', goalRpcProps);
      return renderHtml(rs, pos, html);
    }, [rs, selectedLocs])
    const goal = 
        goalState.state === 'rejected' ?
            <p color='red'>{mapRpcError(goalState.error).message}</p>
        : goalState.state === 'loading' ?
            <>Loading...</>
        : goalState.value

    const movesState = useAsyncPersistent<JSX.Element>(async () => {
        const movesRpcProps: GoalSelectionProps = {
            ...props,
            selectedLocations: [],
            selections: selectedLocs.map(goalsLocationToSubexprPos).filter((p : SubexprPos | undefined) : p is SubexprPos => !!p)
        }
        const html: Html = await rs.call('MotivatedProof.MotivatedProofMovePanel.rpc', movesRpcProps)
        return renderHtml(rs, pos, html)
    }, [rs, selectedLocs])
    const moves =
        movesState.state === 'rejected' ?
            <p color='red'>{mapRpcError(movesState.error).message}</p>
        : movesState.state === 'loading' ?
            <>Loading...</>
        : movesState.value
        
    return (
    <div>
        <LocationsContext.Provider value={locs}>
            { goal }
        </LocationsContext.Provider>
        <hr />
        { moves }
    </div>);
});

export default InfoDisplayContent;