import React, { createContext, useState } from 'react';
import HtmlDisplay, { Html } from './htmlDisplay';
import { DocumentPosition } from '@leanprover/infoview/*';

export const RenderingContext = createContext<React.Dispatch<React.SetStateAction<Html>> | undefined>(undefined);

export default function HtmlReducerRendering(props:{pos:DocumentPosition, initHtml:Html}) : JSX.Element {
    const [html, setHtml] = useState(props.initHtml)

    return (
        <RenderingContext.Provider value={setHtml}>
            <HtmlDisplay pos={props.pos} html={html} />
        </RenderingContext.Provider>
    );
}
