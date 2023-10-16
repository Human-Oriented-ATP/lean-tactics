import * as React from "react"
import ReactDOMServer from 'react-dom/server'
import { DocumentPosition } from "@leanprover/infoview"
import HtmlDisplay, { Html } from "./htmlDisplay"

export default function(props:{pos:DocumentPosition, html:Html}) {
    return (
        <p>
            {ReactDOMServer.renderToStaticMarkup(<HtmlDisplay pos={props.pos} html={props.html} />)}
        </p>
        );
}