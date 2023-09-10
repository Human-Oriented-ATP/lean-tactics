import * as React from 'react';
import { Position, Range, TextEdit, WorkspaceEdit } from 'vscode-languageserver-types';
import { DocumentPosition, EditorContext, RpcContext, useAsync, PanelWidgetProps,
   GoalsLocation, InteractiveGoal, useAsyncPersistent, RpcPtr, mapRpcError } from '@leanprover/infoview';
import { Typography, Button, Grid } from '@mui/material';

export interface MotivatedProofPanelProps extends PanelWidgetProps
{
  buttons : {label : String, text : String, num : number}[]
}

function findGoalForLocation(goals: InteractiveGoal[], loc: GoalsLocation): InteractiveGoal {
  for (const g of goals) {
    if (g.mvarId === loc.mvarId) return g
  }
  throw new Error(`Could not find goal for location ${JSON.stringify(loc)}`)
}

/** Inserts the text at the specified position by calling `makeInsertCommand` from the Lean file,
 *  and switches to a new cursor position.
 */
function insertText(props:{pos:DocumentPosition, text: String, loc:GoalsLocation[], goals:InteractiveGoal[]}) {
  const rpcSession = React.useContext(RpcContext)
  const editorCtx = React.useContext(EditorContext)
  const asyncWSEdit = useAsync<{edit:WorkspaceEdit, newPos:DocumentPosition}>(async () => {
  if (props.loc.length == 0)
  { return await rpcSession.call('makeInsertionCommand', { pos : props.pos, text : props.text}) }
  else 
  { const temp = props.loc.map (loc => 
    { const g = findGoalForLocation(props.goals, loc)
      if (g.ctx === undefined) throw new Error(`Lean server 1.1.2 or newer is required.`)
      return [g.ctx, loc]} 
    )  
    return await rpcSession.call('makeInsertionCommandWithCtx', { pos : props.pos, text : props.text, locations : temp})
  }
  }, [])
  return () => {
    return void (async () => {
      if (asyncWSEdit.state === "resolved") {
        await editorCtx.api.applyEdit(asyncWSEdit.value.edit);
        await editorCtx.revealPosition({...asyncWSEdit.value.newPos, uri: props.pos.uri});
      }
    })()
  };
};

/** A Button UI component that calls the `insertText` function when clicked. */
function InsertionButton(props:{pos:DocumentPosition, loc:GoalsLocation[], goals : InteractiveGoal[], label:String, text:String}): JSX.Element {
  return (<Button
    variant="outlined"
    color="primary"
    size="medium"
    style={{ textTransform: 'none' }}
    onClick={insertText({pos: props.pos, text: props.text, loc: props.loc, goals: props.goals})}>
      {props.label}
      </Button>);
}

/** The main UI panel for displaying motivated proofs. */
export default function motivatedProofPanel
    (props: MotivatedProofPanelProps) {
  return (
  <details open={true}>
    <summary>Motivated proof interface</summary>
    <Typography variant="button" display="block" mt={2} gutterBottom>
      Proof-generating moves
    </Typography>
    <Grid container direction="column" spacing={1}>
      { props.buttons.map ((button:{label:String, text:String, num: number}) => {
          if (props.selectedLocations.length == button.num)
            return (
              <Grid item>
              <InsertionButton pos={props.pos} loc={props.selectedLocations} goals={props.goals} label={button.label} text={button.text} />
              </Grid>);
        }) }
    </Grid>
  </details>
  );
}