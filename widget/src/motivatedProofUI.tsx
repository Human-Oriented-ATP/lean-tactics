import * as React from 'react';
import { Position, Range, TextEdit, WorkspaceEdit } from 'vscode-languageserver-types';
import { DocumentPosition, EditorContext, RpcContext, useAsync } from '@leanprover/infoview';
import { Typography, Button, Grid } from '@mui/material';

/** Inserts the text at the specified position by calling `makeInsertCommand` from the Lean file,
 *  and switches to a new cursor position.
 */
function insertText(props:{pos:DocumentPosition, text: String}) {
  const rpcSession = React.useContext(RpcContext)
  const editorCtx = React.useContext(EditorContext)
  const asyncWSEdit = useAsync<{edit:WorkspaceEdit, newPos:DocumentPosition}>(async () => {
    return await rpcSession.call('makeInsertionCommand', props)
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
function InsertionButton(props:{pos:DocumentPosition, label:String, text:String}): JSX.Element {
  return (<Button
    variant="outlined"
    color="primary"
    size="medium"
    style={{ textTransform: 'none' }}
    onClick={insertText({pos: props.pos, text: props.text})}>
      {props.label}
      </Button>);
}

/** The main UI panel for displaying motivated proofs. */
export default function motivatedProofPanel
    (props:{pos:DocumentPosition, buttons:{label:String, text:String}[]}) {
  return (
  <details open={true}>
    <summary>Motivated proof interface</summary>
    <Typography variant="button" display="block" mt={2} gutterBottom>
      Proof-generating moves
    </Typography>
    <Grid container direction="column" spacing={1}>
      { props.buttons.map ((button:{label:String, text:String}) => {
          return (
            <Grid item>
            <InsertionButton pos={props.pos} label={button.label} text={button.text} />
            </Grid>);
        }) }
    </Grid>
  </details>
  );
}
