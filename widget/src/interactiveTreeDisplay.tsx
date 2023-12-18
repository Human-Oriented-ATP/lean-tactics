import * as React from 'react';
import Tree from 'react-d3-tree';
import { LocationsContext, CodeWithInfos, DocumentPosition, InteractiveCode, GoalsLocation, PanelWidgetProps } from '@leanprover/infoview';
import type { RawNodeDatum, CustomNodeElementProps } from 'react-d3-tree/lib/types/types/common';

export type DisplayTree =
  { node: { label?: CodeWithInfos, children: Array<DisplayTree> } }

export type TreeNodeDatum = RawNodeDatum & { label?: CodeWithInfos }

export type DisplayTreeProps = PanelWidgetProps & { tree : DisplayTree }

function treeToData(tree: DisplayTree): TreeNodeDatum {
    const { label, children } = tree.node
    if (!Array.isArray(children)) {
        throw new Error("Children are not an array")
    }    
    if (children.length == 0) {
        return {
            name: 'node',
            label: label
          }          
    } else {
        const childrenAsTrees = children.map(treeToData)
        return {
            name: 'node',
            label: label,
            children: childrenAsTrees
        }
    }  
}

function renderForeignObjectNode({ nodeDatum }: CustomNodeElementProps, _: DocumentPosition,
  foreignObjectProps: React.SVGProps<SVGForeignObjectElement>): JSX.Element {
  const nodeDatum_ = nodeDatum as TreeNodeDatum
  return (
    <g>
      <rect x="-50" y="-10" width="100" height="20" fill="green" style={{ border: "black" }} />
      <foreignObject {...foreignObjectProps} style={{ textAlign: "center" }}>
        {nodeDatum_.label && <InteractiveCode fmt={nodeDatum_.label} />}
      </foreignObject>
    </g>
  )
}

function centerTree (r : React.RefObject<HTMLDivElement>, t : any, setT : React.Dispatch<any>) {
    React.useLayoutEffect(() => {
        const elt = r.current
        if (elt == null) { return }
        if (t != null) { return }
        const b = elt.getBoundingClientRect()
        if (!b.width || !b.height) { return }
        setT({ x: b.width / 2, y: 20 })
    })
}

export function RenderDisplayTree({ pos, tree, r }: 
    { pos: DocumentPosition, tree: DisplayTree, r : React.RefObject<HTMLDivElement> }): 
    JSX.Element {
    const nodeSize = { x: 120, y: 40 }
    const foreignObjectProps = { width: 100, height: 30, y: -10, x: -50 }
    const [t, setT] = React.useState<any | null>(null)
    centerTree(r, t, setT)
    return (
        <Tree
          data={treeToData(tree)}
          translate={t ?? { x: 0, y: 0 }}
          nodeSize={nodeSize}
          renderCustomNodeElement={rd3tProps =>
            renderForeignObjectNode(rd3tProps, pos, foreignObjectProps)}
          orientation='vertical'
          pathFunc={'straight'} />
    )
}

export default function RenderDisplay(props: DisplayTreeProps) : JSX.Element {
    const pos = props.pos
    const [selectedLocs, setSelectedLocs] = React.useState<GoalsLocation[]>([]);
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
    props.selectedLocations = selectedLocs;
    React.useEffect(() => setSelectedLocs([]), [pos.uri, pos.line, pos.character]);
    const r = React.useRef<HTMLDivElement>(null)
    return (
    <div
      style={{
        height: '400px',
        display: 'inline-flex',
        minWidth: '600px',
        border: '1px solid rgba(100, 100, 100, 0.2)',
        overflow: 'hidden', 
        resize: 'both',
        opacity: '0.9',
      }}
      ref={r}
    >
     <LocationsContext.Provider value = {locs}>
        <RenderDisplayTree pos={pos} tree={props.tree} r={r} />
     </LocationsContext.Provider>
     <div>{selectedLocs.map(loc => {console.log(loc); return <p>Location selected</p>})}</div>
    </div>)
}