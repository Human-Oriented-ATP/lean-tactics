import * as React from "react"
import ReactDOMServer from 'react-dom/server'
import { DocumentPosition } from "@leanprover/infoview"
import HtmlDisplay, { Html } from "./htmlDisplay"

const TestCtx = React.createContext(0)

function TestComponent(props:{pos:DocumentPosition}) {
    const ctx = React.useContext(TestCtx);
    return (<p>Displaying {ctx}.</p>);
}

const testHtml : Html = 
    { component : ["", "", {}, []] }

export default function(props:{pos:DocumentPosition}) {
    return (
    <TestCtx.Provider value={5}>
        <p>{ReactDOMServer.renderToStaticMarkup(<HtmlDisplay pos={props.pos} html={testHtml} />)}</p>
    </TestCtx.Provider>
    );
}