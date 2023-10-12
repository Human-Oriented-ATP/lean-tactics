import * as React from 'react';
import { RpcContext, DocumentPosition, mapRpcError, useAsyncPersistent } from "@leanprover/infoview";
import {RenderingContext} from './reducerRendering';
import HtmlDisplay, { Html } from './htmlDisplay';

interface LspButtonProps {
    pos : DocumentPosition
    label : string
    method : string
}

export default function LspTestButton(props:LspButtonProps) {
    const rs = React.useContext(RpcContext)
    const setHtml = React.useContext(RenderingContext) as React.Dispatch<React.SetStateAction<Html>>
    const onClickButton = async () => {
        const newHtml = useAsyncPersistent<Html>(
            async () => {
                return await rs.call(props.method, props) 
            }, [rs, props.pos])
        if (newHtml.state === 'resolved')
            setHtml(newHtml.value)
        else if (newHtml.state === 'rejected')
            console.log(mapRpcError(newHtml.error).message)
    }
    return (
        <button onClick={onClickButton}>
            {props.label}
        </button>
        );
}