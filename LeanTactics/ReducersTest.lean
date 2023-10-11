import LeanTactics.Reducers
import ProofWidgets.Component.HtmlDisplay

open ProofWidgets Html Jsx

#check HtmlDisplay

#html <LspButton label={"Test"} method={""} />

#html .ofComponent HtmlReducerRendering ⟨<p> Hello World </p>⟩ #[]

-- #html .ofComponent HtmlReducerRendering ⟨testReducer.html testReducer.init⟩ #[]