import React from 'react';
import HtmlDisplay, { Html } from './htmlDisplay';
import { DocumentPosition } from '@leanprover/infoview/*';

interface CheckboxToggleProps {
    pos : DocumentPosition
    message : string
    filtered : Html
    all : Html
    initiallyFiltered : boolean
}

export default function FilterDetails(props: CheckboxToggleProps) {
    const [isFiltered, setFiltered] = React.useState(props.initiallyFiltered);

    return <details open>
        <summary className="mv2 pointer">
            {props.message}
            <span className="fr" onClick={e => { e.preventDefault() }}>
                <a className="link pointer mh2 dim codicon codicon-filter" title="filter"
                    onClick={_ => { setFiltered(s => !s) }} />
            </span>
        </summary>
        <HtmlDisplay pos={props.pos} html={isFiltered ? props.filtered : props.all}/>
    </details>
}