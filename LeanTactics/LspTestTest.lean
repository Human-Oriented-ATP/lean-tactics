import LeanTactics.LspTest

open Lean Server Elab ProofWidgets
open scoped Jsx Json

open Command

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
  -- withFile lspFile .read fun file ↦ do
  let _ ← renderHtml <LspButton label={"Test"} />

#test_lsp