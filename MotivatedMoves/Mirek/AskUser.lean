import Lean
import ProofWidgets
import Mathlib.Tactic

open ProofWidgets.Jsx
open Lean ProofWidgets Server

--    __  __                       _
--   |  \/  | ___  _ __   __ _  __| |
--   | |\/| |/ _ \| '_ \ / _` |/ _` |
--   | |  | | (_) | | | | (_| | (_| |
--   |_|  |_|\___/|_| |_|\__,_|\__,_|
--

inductive IStateM.Result (Q A ε σ α : Type u)
  | terminate : α → σ → IStateM.Result Q A ε σ α
  | throw     : ε → σ → IStateM.Result Q A ε σ α
  | interact  : Q → σ → (A → σ → IStateM.Result Q A ε σ α) → IStateM.Result Q A ε σ α

instance [Inhabited ε] [Inhabited σ] : Inhabited (IStateM.Result Q A ε σ α) := ⟨.throw default default⟩

def IStateM (Q A ε σ α) := σ → IStateM.Result Q A ε σ α

instance [Inhabited ε] : Inhabited (IStateM Q A ε σ α) := ⟨fun s => .throw default s⟩
namespace IStateM

variable {α β Q A ε σ : Type u} [Inhabited ε]

private partial def bind' [Inhabited ε] (x : IStateM Q A ε σ α) (f : α → IStateM Q A ε σ β) : IStateM Q A ε σ β := fun s =>
  match x s with
  | .terminate a s => f a s
  | .throw     e s => .throw e s
  | .interact q s cont => .interact q s fun ans => IStateM.bind' (cont ans) f

@[always_inline, inline]
protected def bind (x : IStateM Q A ε σ α) (f : α → IStateM Q A ε σ β) : IStateM Q A ε σ β := fun s =>
  match x s with
  | .terminate a s => f a s
  | .throw     e s => .throw e s
  | .interact q s cont => .interact q s fun ans => IStateM.bind' (cont ans) f

@[always_inline]
instance : Monad (IStateM Q A ε σ)  where
  pure := .terminate
  bind := IStateM.bind

open EStateM Backtrackable in
@[always_inline, inline]
protected partial def tryCatch {δ} [Backtrackable δ σ] {α} (x : IStateM Q A ε σ α) (handle : ε → IStateM Q A ε σ α)
    : IStateM Q A ε σ α := fun s =>
  let d := save s
  match x s with
  | .throw e s => handle e (restore s d)
  | .interact q s cont => .interact q s fun ans => IStateM.tryCatch (cont ans) handle
  | ok => ok

open EStateM in
instance [Backtrackable δ σ] : MonadExceptOf ε (IStateM Q A ε σ) where
  throw := .throw
  tryCatch := IStateM.tryCatch


def askQuestion (q : Q) : IStateM Q A ε σ A := (.interact q · .terminate)

def giveAnswer (a : A) (x : IStateM Q A ε σ α) : OptionT (StateM σ) (IStateM Q A ε σ α) := fun s =>
  match x s with
  | .interact _ s cont => (some (cont a), s)
  | .terminate _ s
  | .throw     _ s => (none, s)

def runWithAnswers (as : Array A) (x : IStateM Q A ε σ α) : StateM σ (Option α) := OptionT.run do
  let result ← as.foldlM (fun x a => x.giveAnswer a) x
  fun s => match result s with
  | .terminate a s => (some a, s)
  | .throw    _ s
  | .interact _ s _ => (none, s)

def runWithAnswersIO {Q A ε α : Type} (as : Array A) (x : IStateM Q A ε IO.RealWorld α) : BaseIO (Option α) := fun s =>
  let (a, s) := x.runWithAnswers as s
  .ok a s


end IStateM

--     ___                  _   _               _           _
--    / _ \ _   _  ___  ___| |_(_) ___  _ __   (_)_ __  ___| |_ __ _ _ __   ___ ___
--   | | | | | | |/ _ \/ __| __| |/ _ \| '_ \  | | '_ \/ __| __/ _` | '_ \ / __/ _ \
--   | |_| | |_| |  __/\__ \ |_| | (_) | | | | | | | | \__ \ || (_| | | | | (_|  __/
--    \__\_\\__,_|\___||___/\__|_|\___/|_| |_| |_|_| |_|___/\__\__,_|_| |_|\___\___|
--

inductive UserQuestion : Type where
| empty
| form (elems : Array Html)
| select (question : Html) (array : Array Html)
| custom (code : Html)
| editDocument (edit : Lsp.TextDocumentEdit)
| error (data : WithRpcRef MessageData)
instance UserQuestion.Inhabited : Inhabited UserQuestion where
  default := .empty

instance : RpcEncodable UserQuestion where
  rpcEncode q := match q with
  | .empty => return Json.mkObj [("kind", "empty")]
  | .form elems => do
    let elems ← elems.mapM rpcEncode
    return Json.mkObj [("kind", "form"), ("elems", Json.arr elems)]
  | .select question options => do
    let question ← rpcEncode question
    let options ← options.mapM rpcEncode
    return Json.mkObj [("kind", "select"), ("question",question),
    ("options", Json.arr options)]
  | .custom code => do
    let code ← rpcEncode code
    return Json.mkObj [("kind", "custom"), ("code", code)]
  | .editDocument edit => do
    let edit ← rpcEncode edit
    return Json.mkObj [("kind", "editDocument"), ("edit", edit)]
  | .error data => do
    let data ← rpcEncode data
    return Json.mkObj [("kind", "error"), ("data",data)]
  rpcDecode json := do
    let kind ← json.getObjVal? "kind"
    let kind ← kind.getStr?
    match kind with
    | "empty" =>
      return .empty
    | "form" => do
      let elems ← json.getObjVal? "elems"
      let elems ← elems.getArr?
      let elems : Array Html ← elems.mapM rpcDecode
      return .form elems
    | "select" =>
      let question ← json.getObjVal? "question"
      let question : Html ← rpcDecode question
      let options ← json.getObjVal? "options"
      let options ← options.getArr?
      let options : Array Html ← options.mapM rpcDecode
      return .select question options
    | "custom" => do
      let msg ← json.getObjVal? "msg"
      let msg : Html ← rpcDecode msg
      return .custom msg
    | "editDocument" => do
      let edit ← json.getObjVal? "edit"
      let edit : Lsp.TextDocumentEdit ← rpcDecode edit
      return .editDocument edit
    | "error" => do
      let data ← json.getObjVal? "data"
      let data : WithRpcRef MessageData ← rpcDecode data
      return .error data
    | _ => .error s!"Invalid kind: {kind}"

abbrev InteractiveIO := ReaderT RequestContext <| IStateM UserQuestion Json (Exception ⊕ String) IO.RealWorld

def throwWidgetError (e : String) : InteractiveIO α := throw (.inr e)

--    ____                  _  __ _
--   / ___| _ __   ___  ___(_)/ _(_) ___
--   \___ \| '_ \ / _ \/ __| | |_| |/ __|
--    ___) | |_) |  __/ (__| |  _| | (__
--   |____/| .__/ \___|\___|_|_| |_|\___|
--         |_|
--                          _   _
--     __ _ _   _  ___  ___| |_(_) ___  _ __  ___
--    / _` | | | |/ _ \/ __| __| |/ _ \| '_ \/ __|
--   | (_| | |_| |  __/\__ \ |_| | (_) | | | \__ \
--    \__, |\__,_|\___||___/\__|_|\___/|_| |_|___/
--       |_|

def askUser (q : UserQuestion) : InteractiveIO Json := fun _ => IStateM.askQuestion q

def askUserForm (form : Html) : InteractiveIO Json := do
  let .element "form" _ elems := form | throwWidgetError "Not an Html form"
  askUser (.form elems)
open ProofWidgets.Jsx in
def askUserInput (title input : Html) : InteractiveIO String := do
  let .element "input" inputAttrs inputElems := input | throwWidgetError "Not an Html input"
  let inputAttrs := inputAttrs.push ("name", "query")
  let input := Html.element "input" inputAttrs inputElems
  let submit := <input type="submit"/>
  let answer ← askUser (.form #[title, input, submit])
  match answer.getObjValAs? String "query" with
  | .error err => throwWidgetError err
  | .ok answer => return answer

def askUserString (question : Html) : InteractiveIO String :=
  askUserInput question <input type="string"/>
def askUserInt (question : Html) : InteractiveIO Int := do
  let answer ← askUserInput question <input type="number" defaultValue="0"/>
  let some answer := answer.toInt? | throwWidgetError "not an integer"
  return answer
def askUserSelect {α : Type} (question : Html) (options : List (α × Html))
  : InteractiveIO α := do
  match fromJson? (← askUser (.select question (options.map Prod.snd).toArray)) with
  | .error err => throwWidgetError err
  | .ok (answer : Nat) => do
    let some (answer,_) := options.get? answer | throwWidgetError "Index out of bounds"
    return answer
def askUserBool (question : Html) : InteractiveIO Bool
  := askUserSelect question [
    (true, <button>Yes</button>),
    (false, <button>No</button>)
  ]
def askUserConfirm (message : Html) : InteractiveIO Unit
  := askUserSelect message [((), <button>OK</button>)]

def editDocument (edits : Array Lsp.TextEdit) : InteractiveIO Unit
  := do
    let ctx : RequestContext ← read
    let meta := ctx.doc.meta
    _ ← askUser (.editDocument {
      textDocument := { uri := meta.uri, version? := meta.version }
      edits := edits
    })
    return

def insertLine (lineNo : Nat) (line : String) : InteractiveIO Unit :=
  let pos : Lsp.Position := { line := lineNo, character := 0 }
  editDocument #[{ range := { start := pos, «end» := pos }, newText := line++"\n" }]

--   __        ___     _            _
--   \ \      / (_) __| | __ _  ___| |_
--    \ \ /\ / /| |/ _` |/ _` |/ _ \ __|
--     \ V  V / | | (_| | (_| |  __/ |_
--      \_/\_/  |_|\__,_|\__, |\___|\__|
--                       |___/

def runWidget (x : InteractiveIO Unit) : RequestM (UserQuestion × (Json → InteractiveIO Unit)) := fun ctx => do
  match x ctx (← EStateM.get) with
  | .interact q s cont =>
    EStateM.set s
    return (q, fun json _ => cont json)

  | .terminate () s =>
    EStateM.set s
    return (.empty, fun _ => pure ())

  | .throw (.inl e) s =>
    EStateM.set s
    return (.error (WithRpcRef.mk e.toMessageData), fun _ => pure ())

  | .throw (.inr e) s =>
    EStateM.set s
    return (.select <p><b>Widget Error: </b>{.text e}</p> #[<button>OK</button>], fun _ => pure ())

def InteractiveMUnit := InteractiveIO Unit
deriving instance TypeName for InteractiveMUnit

instance : RpcEncodable (InteractiveIO Unit) where
  rpcEncode x := rpcEncode (⟨x⟩ : WithRpcRef InteractiveMUnit)
  rpcDecode json := do
    let out : WithRpcRef InteractiveMUnit ← rpcDecode json
    return out.val

def JsonToInteractiveMUnit := Json → InteractiveIO Unit
deriving instance TypeName for JsonToInteractiveMUnit

@[server_rpc_method]
def initializeInteraction (code : InteractiveIO Unit) : RequestM (RequestTask (UserQuestion × WithRpcRef JsonToInteractiveMUnit)) :=
  RequestM.asTask do
    let (question, cont) ← runWidget code
    return (question, WithRpcRef.mk cont)

@[server_rpc_method]
def processUserAnswer
  (args : Json × (WithRpcRef JsonToInteractiveMUnit))
  : RequestM (RequestTask (UserQuestion × (WithRpcRef JsonToInteractiveMUnit))) :=
  RequestM.asTask do
    let (answer, cont) := args
    let (question, cont2) ← runWidget (cont.val answer)
    return (question, WithRpcRef.mk cont2)

--    _____          _   _      ___ __  __
--   |_   _|_ _  ___| |_(_) ___|_ _|  \/  |
--     | |/ _` |/ __| __| |/ __|| || |\/| |
--     | | (_| | (__| |_| | (__ | || |  | |
--     |_|\__,_|\___|\__|_|\___|___|_|  |_|
--

instance : STWorld IO.RealWorld InteractiveIO where

instance : MonadLift (EIO Exception) InteractiveIO where
  monadLift x := fun _ s =>
    match x s with
    | .ok x s => .terminate x s
    | .error e s => .throw (.inl e) s

open Elab Tactic

abbrev CoreIM     := ReaderT Core.Context <| StateRefT Core.State InteractiveIO
abbrev MetaIM     := ReaderT Meta.Context <| StateRefT Meta.State CoreIM
abbrev TermElabIM := ReaderT Term.Context <| StateRefT Term.State MetaIM
abbrev TacticIM   := ReaderT Tactic.Context <| StateRefT Tactic.State TermElabIM

variable [Monad n] [Monad m] [MonadLiftT (ST ω) m] [MonadLiftT (ST ω) n]

private def liftReaderState [MonadLift m n] : MonadLift (ReaderT ρ (StateRefT' ω σ m)) (ReaderT ρ (StateRefT' ω σ n)) where
  monadLift x := fun c => do
    let state1 ← get
    let (out, state2) ← (x c).run state1
    set state2
    return out

instance : MonadLift CoreM CoreIM := liftReaderState
instance : MonadLift MetaM MetaIM := liftReaderState
instance : MonadLift TermElabM TermElabIM := liftReaderState
instance : MonadLift TacticM TacticIM := liftReaderState

private def separateReaderState (finalize : m α → n (InteractiveIO α)) (x : ReaderT ρ (StateRefT' ω σ m) α)
    : ReaderT ρ (StateRefT' ω σ n) (InteractiveIO α) :=
  fun c => do finalize ((x c).run' (← get))

def CoreIM.run     : CoreIM α     → CoreM     (InteractiveIO α) := separateReaderState pure
def MetaIM.run     : MetaIM α     → MetaM     (InteractiveIO α) := separateReaderState CoreIM.run
def TermElabIM.run : TermElabIM α → TermElabM (InteractiveIO α) := separateReaderState MetaIM.run
def TacticIM.run   : TacticIM α   → TacticM   (InteractiveIO α) := separateReaderState TermElabIM.run
