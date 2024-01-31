import * as React from 'react';
import { RpcContext } from '@leanprover/infoview';

export default function FormInput(props:any) {
    const rs = React.useContext(RpcContext)

    async function relay(formData:FormData) {
        const result = Object.fromEntries(formData)
        await rs.call('Form.rpc', result)
    }

    function handleSubmit(event: React.FormEvent<HTMLFormElement>) {
        event.preventDefault()
        const formData = new FormData(event.currentTarget)
        relay(formData)
    }

    return (
        <form onSubmit={handleSubmit}>
            {props.children}
        </form>
    );
  }