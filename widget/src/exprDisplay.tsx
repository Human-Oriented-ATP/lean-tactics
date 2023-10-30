import * as React from 'react'
import {LocationsContext, InteractiveCode, TaggedText, GoalsLocation, SubexprInfo, DocumentPosition } from '@leanprover/infoview';

export interface ExprSelectionProps {
  pos: DocumentPosition
  expr: TaggedText<SubexprInfo>
  subexprPos: string
}

export const InfoDisplayContent = React.memo((props : ExprSelectionProps) => {
  console.log("Showing expr ")
  console.log(props)
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
      subexprTemplate: { mvarId: '', loc: { target: props.subexprPos }}
  }), [selectedLocs]);
  return (
  <div>
      (<LocationsContext.Provider value = {locs}>
          {InteractiveCode({fmt : props.expr})}
      </LocationsContext.Provider>)
      <p>The number of selected locations: {selectedLocs.length}</p>
  </div>
  )
})

export interface ExprDisplayProps extends ExprSelectionProps {
  description : string
}

export default function(props:{exprs : ExprDisplayProps[]}) {
  console.log("Rendering")
  console.log(props);
  return (
  <div>
    { props.exprs.map((prop:ExprDisplayProps) =>
      <div>
        <p>{prop.description}</p>
        <InfoDisplayContent pos={prop.pos} expr={prop.expr} subexprPos={prop.subexprPos} />
      </div>
      ) }
  </div>
  );
}
