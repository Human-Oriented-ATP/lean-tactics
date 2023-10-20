import * as React from 'react';
import { RpcContext, DocumentPosition, mapRpcError, useAsyncPersistent, useAsync } from "@leanprover/infoview";
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
    const onClickButton = () => {
        const st = useAsync<Html>(async () => {
            return await rs.call(props.method, props)
        }, [rs, props])
        if (st.state === 'resolved')
            setHtml(st.value)
        else if (st.state === 'rejected')
            console.log(mapRpcError(st.error).message)
        }
    return (
        <button onClick={onClickButton}>
            {props.label}
        </button>
        );
}