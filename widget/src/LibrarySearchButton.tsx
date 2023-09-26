/*
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers, Wojciech Nawrocki

Modified from `htmlDisplay.tsx` and `makeEditLink.tsx` in the `ProofWidgets` repository. 
*/

import React, { useState } from 'react';
import { EditorContext, DocumentPosition, RpcContext, RpcSessionAtPos, 
    importWidgetModule, mapRpcError, useAsyncPersistent, EditorConnection } from '@leanprover/infoview';
import type { DynamicComponent } from '@leanprover/infoview';
import { Range, TextDocumentEdit } from 'vscode-languageserver-protocol';
import { Button } from '@mui/material'
import '@mui/private-theming'

interface LibrarySearchProps {
    suggestion : string
    pos : DocumentPosition
    range : Range
}

export default function LibrarySearchButton (props : LibrarySearchProps) {
    const ec = React.useContext(EditorContext)
    function onClick() {
        ec.api.applyEdit({
          changes: { [props.pos.uri]: [{range : props.range, newText: props.suggestion }] }
        })
      }
    return <Button color = {'primary'} size = {'medium'} sx={{textTransform: "none"}} variant = {'outlined'} onClick={onClick}>{props.suggestion}</Button>
}