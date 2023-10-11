import React, { createContext, useState } from 'react';
import { DocumentPosition } from "@leanprover/infoview"
import HtmlDisplay, { Html } from "./htmlDisplay"

export default function HtmlReducerRendering({pos, initHtml}:{pos:DocumentPosition, initHtml:Html}) : JSX.Element {
    const [html, setHtml] = useState(initHtml)

    return (
            <HtmlDisplay pos={pos} html={html} />
    );
}