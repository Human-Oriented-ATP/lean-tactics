/*
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers, Wojciech Nawrocki

Modified from `htmlDisplay.tsx` and `makeEditLink.tsx` in the `ProofWidgets` repository. 
*/

import React, { useState } from 'react';
import { EditorContext, DocumentPosition } from '@leanprover/infoview';
import { TextDocumentEdit } from 'vscode-languageserver-protocol';
import { Button, ButtonPropsVariantOverrides, ButtonPropsColorOverrides, ButtonPropsSizeOverrides } from '@mui/material'
import { OverridableStringUnion } from '@mui/types'
import '@mui/private-theming'
import HtmlDisplay, { Html } from './htmlDisplay';
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

    async function onClick() {
        setHTMLVisible(true);
        
        if (props.edit) {
            await ec.api.applyEdit({ documentChanges: [props.edit.edit] })
            if (props.edit.newCursorPos)
                await ec.revealPosition({ ...props.edit.newCursorPos, uri: props.edit.edit.textDocument.uri })
            
        }
    }
    return (
        <>
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
                <HtmlDisplay pos={props.pos} html={props.html} /> : null }
        </>
    );
}