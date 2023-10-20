import * as React from "react"
import { DocumentPosition } from "@leanprover/infoview"
import HtmlDisplay, { Html } from "./htmlDisplay"

export const RenderingContext = React.createContext<React.Dispatch<React.SetStateAction<Html>> | undefined>(undefined);

export default function HtmlDisplayPanel({pos, html} : {pos: DocumentPosition, html: Html}): JSX.Element {
  const [output, setOutput] = React.useState(html);

  return (
    <RenderingContext.Provider value={setOutput}>
        <details open>
        <HtmlDisplay pos={pos} html={output} />
        </details>
    </RenderingContext.Provider> );
}