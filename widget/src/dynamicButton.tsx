/*
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers, Wojciech Nawrocki

Modified from `htmlDisplay.tsx` and `makeEditLink.tsx` in the `ProofWidgets` repository. 
*/

import React, { useState } from 'react';
import { EditorContext, DocumentPosition, RpcContext, RpcSessionAtPos, 
    importWidgetModule, mapRpcError, useAsyncPersistent } from '@leanprover/infoview';
import type { DynamicComponent } from '@leanprover/infoview';
import { TextDocumentEdit } from 'vscode-languageserver-protocol';
import { Button, ButtonPropsVariantOverrides, ButtonPropsColorOverrides, ButtonPropsSizeOverrides } from '@mui/material'
import { OverridableStringUnion } from '@mui/types'
import '@mui/private-theming'

type HtmlAttribute = [string, any]

export type Html =
    | { element: [string, HtmlAttribute[], Html[]] }
    | { text: string }
    | { component: [string, string, any, Html[]] }

/**
 * Render a HTML tree into JSX, resolving any dynamic imports corresponding to `component`s along
 * the way.
 *
 * This guarantees that the resulting React tree is exactly as written down in Lean. In particular,
 * there are no extraneous {@link DynamicComponent} nodes which works better with some libraries
 * that directly inspect the children nodes.
 */
async function renderHtml(rs: RpcSessionAtPos, pos: DocumentPosition, html: Html):
        Promise<JSX.Element> {
    if ('text' in html) {
        return <>{html.text}</>
    } else if ('element' in html) {
        const [tag, attrsList, cs] = html.element
        const attrs: any = {}
        for (const [k,v] of attrsList) {
            attrs[k] = v
        }
        const children = await Promise.all(cs.map(async html => await renderHtml(rs, pos, html)))
        if (tag === "hr") {
            // React is greatly concerned by <hr/>s having children.
            return <hr/>
        } else if (children.length === 0) {
            return React.createElement(tag, attrs)
        } else {
            return React.createElement(tag, attrs, children)
        }
    } else if ('component' in html) {
        const [hash, export_, props, cs] = html.component
        const children = await Promise.all(cs.map(async html => await renderHtml(rs, pos, html)))
        const dynProps = {...props, pos}
        const mod = await importWidgetModule(rs, pos, hash)
        if (!(export_ in mod)) throw new Error(`Module '${hash}' does not export '${export_}'`)
        if (children.length === 0) {
            return React.createElement(mod[export_], dynProps)
        } else {
            return React.createElement(mod[export_], dynProps, children)
        }
    } else {
        return <span className="red">Unknown HTML variant: {JSON.stringify(html)}</span>
    }
}

function HtmlDisplay({pos, html} : {pos: DocumentPosition, html: Html}):
        JSX.Element {
    const rs = React.useContext(RpcContext)
    const state = useAsyncPersistent(() => renderHtml(rs, pos, html), [rs, pos, html])
    if (state.state === 'resolved')
        return state.value
    else if (state.state === 'rejected')
        return <span className="red">Error rendering HTML: {mapRpcError(state.error).message}</span>
    return <></>
}

interface EditParams {
    edit : TextDocumentEdit
    newCursorPos? : DocumentPosition
}

interface DynamicButtonStylingProps {
    variant : OverridableStringUnion<'text' | 'outlined' | 'contained', ButtonPropsVariantOverrides>
    color : OverridableStringUnion<'inherit' | 'primary' | 'secondary' | 'success' | 'error' | 'info' | 'warning', ButtonPropsColorOverrides >
    size : OverridableStringUnion<'small' | 'medium' | 'large', ButtonPropsSizeOverrides>
}

interface DynamicButtonProps extends DynamicButtonStylingProps {
    pos : DocumentPosition
    label : string
    edit? : EditParams
    html? : Html
    vanish : boolean
}

export default function DynamicButton(props:DynamicButtonProps) {
    const [isHTMLVisible, setHTMLVisible] = useState(false);
    const ec = React.useContext(EditorContext)

    async function onClick () {
        setHTMLVisible(true);
        
        if (props.edit) {
            await ec.api.applyEdit({ documentChanges: [props.edit.edit] })
            // TODO: https://github.com/leanprover/vscode-lean4/issues/225
            if (props.edit.newCursorPos)
                await ec.revealPosition({ ...props.edit.newCursorPos, uri: props.edit.edit.textDocument.uri })
            
        }
        setHTMLVisible(false); // temporary while states are leaking
    }
    var render = document.getElementById("Grid")
    return (
        <div>
            { (isHTMLVisible && props.vanish) ? null : 
                <Button 
                    variant = {props.variant}
                    color = {props.color} 
                    size = {props.size} 
                    sx={{textTransform: "none"}} 
                    onClick={onClick}>
                        {props.label}
                </Button> }
            { (isHTMLVisible && props.html) ? 
                (render as HTMLElement).style.display = 'none' : null }
        </div>
    );
}