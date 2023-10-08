import Lean
import ProofWidgets

open Lean Server Elab ProofWidgets
open scoped Jsx Json

structure LspButtonProps where
  label : String
deriving ToJson, FromJson

#mkrpcenc PUnit

def leanServerCmd : IO.Process.SpawnArgs := {
  cmd  := "lake"
  args := #["serve"]
  cwd  := ".."
  stdin  := .piped
  stdout := .piped
  stderr := .piped
}

initialize leanServerProcessRef : IO.Ref (Option <| IO.Process.Child leanServerCmd.toStdioConfig) ← IO.mkRef none 

def getLeanServerProcess : IO (IO.Process.Child leanServerCmd.toStdioConfig) := do
  match ← leanServerProcessRef.get with
    | some child => return child
    |    none    =>
      let child ← IO.Process.spawn leanServerCmd
      leanServerProcessRef.set child
      return child

@[server_rpc_method]
def registerNotification (props : LspButtonProps) : RequestM (RequestTask Unit) := do
  let child ← getLeanServerProcess
  let contents := (toJson props).compress
  child.stdin.putStrLn contents
  child.stdin.flush
  IO.FS.writeFile "./lsp_test.txt" contents
  return .pure () 

@[widget_module]
def LspButton : Component LspButtonProps where
  javascript := include_str "../build/js/lspTestButton.js"

-- modified from `savePanelWidgetInfo` to exclude `MonadNameGenerator`

/-- Save the data of a panel widget which will be displayed whenever the text cursor is on `stx`.
`id` must be the name of a definition annotated with `@[widget_module]`. See `PanelWidgetProps`. -/
def savePanelWidgetInfo' [Monad m] [MonadInfoTree m] 
    (stx : Syntax) (id : Name) (props : LazyEncodable Json) : m Unit := do
  let infoId := `panelWidget
  pushInfoLeaf <| .ofUserWidgetInfo {
    stx
    widgetId := ``metaWidget
    props := json% {
      infoId : $(infoId)
    }
  }
  let wi : PanelWidgetInfo := { id, props, infoId }
  pushInfoLeaf <| .ofCustomInfo { stx, value := Dynamic.mk wi }