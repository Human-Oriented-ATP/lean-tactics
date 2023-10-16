import * as React from 'react'
import ReactDOMServer from 'react-dom/server'
import { DocumentPosition } from '@leanprover/infoview'

export default function(props:{pos:DocumentPosition}) {
    return React.createElement('p', ReactDOMServer.renderToStaticMarkup(
        React.createElement('span', 'Testing static mark-up rendering')))
}