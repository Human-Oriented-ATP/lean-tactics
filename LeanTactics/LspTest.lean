import Lean
import ProofWidgets

open Lean Server Elab Command ProofWidgets
open scoped Jsx Json

def lspFile : System.FilePath := "./lsp-test.txt"


structure Props where
  contents : Json 
deriving ToJson, FromJson

instance : ToJson Props where
  toJson := Props.contents

instance : FromJson Props where
  fromJson? := (pure <| .mk ·)


#mkrpcenc PUnit

-- Generalisation of `IO.FS.withFile`
open IO FS System in
@[inline]
def withFile [Monad M] [MonadLiftT IO M] (fn : FilePath) (mode : Mode) (f : Handle → M α) : M α :=
  Handle.mk fn mode >>= f

@[server_rpc_method]
def registerNotification (props : Props) : RequestM (RequestTask Unit) := do
  let contents := (toJson props).compress
  withFile lspFile .append fun file ↦ do
    file.putStrLn contents
    file.flush
  return .pure () 


structure LspButtonProps where
  label : String
deriving ToJson, FromJson

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

def CommandElabM.toIO (x : CommandElabM α) : CommandElabM (IO α) :=
  return EIO.toIO (fun _ ↦ .userError "Failed to run `CommandElabM` to `IO`.") <| 
    x |>.run (← read) |>.run' (← get)

def renderHtml (html : Html) : CommandElabM (Task (Except IO.Error Unit)) := do
  let saveWidget ← CommandElabM.toIO <| 
    savePanelWidgetInfo' (← getRef) ``HtmlDisplay <| do 
      return json% { html : $(← rpcEncode html) }
  IO.asTask saveWidget
  
elab "#test_lsp" : command => do
  unless (← lspFile.pathExists) do
    IO.FS.writeFile lspFile ""
  withFile lspFile .read fun file ↦ do
    let _ ← renderHtml <LspButton label={"Test"} />
    -- let msg ← file.getLine
    -- let _ ← renderHtml <span>{.text s!"Received {msg}"}</span>  