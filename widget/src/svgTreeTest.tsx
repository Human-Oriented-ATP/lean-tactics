import * as React from 'react';
import { LocationsContext, importWidgetModule, RpcSessionAtPos, RpcContext, useAsyncPersistent, mapRpcError, GoalsLocation, DocumentPosition, CodeWithInfos, SubexprPos } from '@leanprover/infoview';

type HtmlAttribute = [string, any]

export type Html =
    | { element: [string, HtmlAttribute[], Html[]] }
    | { text: string }
    | { component: [string, string, any, Html[]] }

/**
 * Render a HTML tree into JSX, resolving any dynamic imports corresponding to `component`s along
 * the way.
 *
 * This guarantees that the resulting React tree is exactly as written down in Lean. In particular,
 * there are no extraneous {@link DynamicComponent} nodes which works better with some libraries
 * that directly inspect the children nodes.
 */
async function renderHtml(rs: RpcSessionAtPos, pos: DocumentPosition, html: Html):
        Promise<JSX.Element> {
    if ('text' in html) {
        return React.createElement(React.Fragment, null, html.text)
    } else if ('element' in html) {
        const [tag, attrsList, cs] = html.element
        const attrs: any = {}
        for (const [k,v] of attrsList) {
            attrs[k] = v
        }
        const children = await Promise.all(cs.map(async html => await renderHtml(rs, pos, html)))
        if (tag === "hr") {
            // React is greatly concerned by <hr/>s having children.
            return React.createElement('hr')
        } else if (children.length === 0) {
            return React.createElement(tag, attrs)
        } else {
            return React.createElement(tag, attrs, children)
        }
    } else if ('component' in html) {
        const [hash, export_, props, cs] = html.component
        const children = await Promise.all(cs.map(async html => await renderHtml(rs, pos, html)))
        const dynProps = {...props, pos}
        const mod = await importWidgetModule(rs, pos, hash)
        if (!(export_ in mod)) throw new Error(`Module '${hash}' does not export '${export_}'`)
        if (children.length === 0) {
            return React.createElement(mod[export_], dynProps)
        } else {
            return React.createElement(mod[export_], dynProps, children)
        }
    } else {
        return React.createElement('span', {className:'red', children:["Unknown HTML variant: ", JSON.stringify(html)]})
    }
}

interface GoalSelectionProps {
    pos : DocumentPosition
    locations : SubexprPos[]
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

const InfoDisplayContent = React.memo((props : GoalSelectionProps) => {
    console.log(props);
    const rs = React.useContext(RpcContext)
    const pos = props.pos
    const [selectedLocs, setSelectedLocs] = React.useState<GoalsLocation[]>(props.locations.map (pos => {return {mvarId: '', loc: {target: pos}}}));
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
        subexprTemplate: { mvarId: '', loc: { target: '/' }}
    }), [selectedLocs]);
    const goalState = useAsyncPersistent<JSX.Element>(async () => {
      const rpcProps:GoalSelectionProps = {
        ...props,
        locations : selectedLocs.map(goalsLocationToSubexprPos).filter((p : SubexprPos | undefined) : p is SubexprPos => !!p) }
      const html:Html = await rs.call('renderTree', rpcProps);
      return renderHtml(rs, pos, html);
    }, [rs, selectedLocs])
    const goal = 
        goalState.state === 'rejected' ?
            <p color='red'>{mapRpcError(goalState.error).message}</p>
        : goalState.state === 'loading' ?
            <>Loading...</>
        : goalState.value
    return (
    <div>
        <LocationsContext.Provider value={locs}>
            {goal}
        </LocationsContext.Provider>
    </div>);
});

export default InfoDisplayContent;