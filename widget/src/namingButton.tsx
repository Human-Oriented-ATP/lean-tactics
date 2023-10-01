import React from 'react'
import { DocumentPosition, SubexprPos, EditorContext } from '@leanprover/infoview'
import { TextDocumentEdit } from 'vscode-languageserver-protocol';
import { TextField } from '@mui/material';

interface NamingButtonProps {
  selectedPos : string
}

export default function NamingButton (props : NamingButtonProps) {
    const ec = React.useContext(EditorContext)
    const pos = props.selectedPos;
    let value = "";
    return (
<div>
        <TextField  inputProps={{ style: { color: "white" } }}
                    variant = {'outlined'}
                    color = {'secondary'} 
                    size = {'medium'} 
                    sx={{textTransform: "none"}} type="text" onChange = {event => value = event.target.value}
                    onKeyDown = {(ev) => {
                        console.log(`Pressed keyCode ${ev.key}`);
                        if (ev.key === 'Enter') {
                          // Do code here
                          if (value !== "") {
                            ec.copyToCode("tree_name ".concat (value, " ", pos));
                          }
                        }
                      }} placeholder="Enter a variable name..." name={"NameBox"}/> 
</div>
    )
}