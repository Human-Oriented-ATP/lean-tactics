import * as React from 'react';
import { RpcContext, DocumentPosition, RpcSessionAtPos } from "@leanprover/infoview";

async function dispatchUpdate(rs:RpcSessionAtPos, message:object) {
    return await rs.call('registerNotification', message)
}

export default function LspTestButton(props:{pos:DocumentPosition, label:string}) {
    const rs = React.useContext(RpcContext)
    return (
        <button onClick={() => dispatchUpdate(rs, props)}>
            {props.label}
        </button>
        );
}