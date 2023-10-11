import * as React from 'react';
import { RpcContext, DocumentPosition } from "@leanprover/infoview";
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
        const newHtml : Html = await rs.call(props.method, props)
        setHtml(newHtml);
    }
    return (
        <button onClick={onClickButton}>
            {props.label}
        </button>
        );
}