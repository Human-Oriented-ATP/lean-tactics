import * as React from "react"
import ReactDOMServer from 'react-dom/server'
import { DocumentPosition } from "@leanprover/infoview"
import HtmlDisplay, { Html } from "./htmlDisplay"

export default function({pos, html}:{pos:DocumentPosition, html:Html}) {
    return (
        <p>
            {ReactDOMServer.renderToStaticMarkup(<HtmlDisplay pos={pos} html={html} />)}
        </p>
        );
}