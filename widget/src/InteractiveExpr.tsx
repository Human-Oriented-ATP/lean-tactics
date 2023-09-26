import React, { useState } from 'react';
import { EditorContext, RpcPtr, DocumentPosition, RpcContext, RpcSessionAtPos, TaggedText,
    importWidgetModule, mapRpcError, useAsyncPersistent, EditorConnection, GoalsLocation, LocationsContext, PanelWidgetProps, InteractiveCode, SubexprInfo } from '@leanprover/infoview';
import { Range, TextDocumentEdit } from 'vscode-languageserver-protocol';


type ExprWithCtx = RpcPtr<'ProofWidgets.ExprWithCtx'>

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
        subexprTemplate: undefined
    }), [selectedLocs]);
    /* Adding {' '} to manage string literals properly: https://reactjs.org/docs/jsx-in-depth.html#string-literals-1 */
    return (<LocationsContext.Provider value = {locs}>
        {   InteractiveCode({fmt : props.expr}) }
    </LocationsContext.Provider>);
})