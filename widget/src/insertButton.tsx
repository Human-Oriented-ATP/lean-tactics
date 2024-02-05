import * as React from 'react';
import { TextDocumentEdit } from 'vscode-languageserver-protocol';
import { EditorContext, DocumentPosition, RpcContext, RpcSessionAtPos, importWidgetModule, mapRpcError, useAsyncPersistent } from '@leanprover/infoview';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faUndo, faRedo, faCoffee } from '@fortawesome/free-solid-svg-icons'

interface EditParams {
    edit : TextDocumentEdit
    newCursorPos? : DocumentPosition
}
interface InsertButtonProps {
    pos : DocumentPosition
    icon : "cw" | "ccw"
    color : "white" | "blue" | "red" | "yellow" | "green" | "orange" | "empty"
    edit : EditParams
}

const name_to_icon = {
    "cw" : faRedo,
    "ccw" : faUndo,
}
const rubikscolor_to_webcolor = {
    "white" : "snow",
    "blue" : "blue",
    "red" : "red",
    "yellow" : "yellow",
    "green" : "green",
    "orange" : "darkorange",
    "empty" : "dimgray",
  }
  
export default function InsertButton(props : InsertButtonProps)
{
    const ec = React.useContext(EditorContext)

    async function onClick () {
                if (props.edit) {
            await ec.api.applyEdit({ documentChanges: [props.edit.edit] })
            if (props.edit.newCursorPos)
                await ec.revealPosition({ ...props.edit.newCursorPos, uri: props.edit.edit.textDocument.uri })
            
        }
    }
    const icon = name_to_icon[props.icon]
    // const icon = faCoffee
    return <button style={{backgroundColor: props.color}} onClick={onClick}><FontAwesomeIcon icon={icon} /></button>
}
