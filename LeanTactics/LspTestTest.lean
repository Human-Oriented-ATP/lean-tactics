import LeanTactics.LspTest

open Lean Server Elab ProofWidgets
open scoped Jsx Json

open Command

@[widget_module]
def HtmlView : Component HtmlDisplayProps where
  javascript := include_str "../build/js/htmlView.js"

#html <HtmlView html={<p> Testing </p>} />

-- #eval show IO String from do
--   let stdin ← IO.getStdin
--   let stdout ← IO.getStdout
--   stdin.putStrLn "Hello"
--   stdin.flush
--   let text ← stdout.getLine
--   return text

-- elab stx:"#lsp_test" : command => do
--   let child ← getLeanServerProcess
--   savePanelWidgetInfo' stx ``HtmlDisplay do
--     return json% { html : $(← rpcEncode <LspButton label={"Test"} />)}
--   let t ← IO.asTask <| do
--     let out ← child.stdin.getLine
--     IO.FS.writeFile "./click_test.txt" out
elab "#test_lsp" : command => do
  unless (← lspFile.pathExists) do
    IO.FS.writeFile lspFile ""
  withFile "./lsp-out.txt" .append fun outFile ↦ do
  withFile lspFile .read fun file ↦ do
    savePanelWidgetInfo' (← getRef) ``HtmlDisplay <| do
      return json% { html : $(← rpcEncode <LspButton label={s!"Test"} />) }
    let contents ← file.getLine
    outFile.putStrLn contents

#test_lsp