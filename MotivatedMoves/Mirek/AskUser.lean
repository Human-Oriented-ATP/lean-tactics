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

namespace InteractiveT

private structure Spec (Q A E : Type u) (m : Type u → Type u) where
  interactM : Type u → Type u
  pure      : α → interactM α
  interact  : Q → (A → (interactM α)) → interactM α
  throw     : E → interactM α
  squash    : m (interactM α) → interactM α
  elim      : [Inhabited E] → [Monad m] → interactM α → (α → m β) → (Q → (A → interactM α) → m β) → (E → m β) → m β

instance : Inhabited (Spec Q A E m) where
  default := {
    interactM := fun _       => PUnit
    pure      := fun _       => ⟨⟩
    interact  := fun _ _     => ⟨⟩
    throw     := fun _       => ⟨⟩
    squash    := fun _       => ⟨⟩
    elim      := fun _ _ _ f => f default
  }

private unsafe inductive InteractiveTImpl (Q A E : Type u) (m : Type u → Type u) (α : Type u)
  | pure     : α → InteractiveTImpl Q A E m α
  | interact : Q → (A → InteractiveTImpl Q A E m α) → InteractiveTImpl Q A E m α
  | throw    : E → InteractiveTImpl Q A E m α
  | squash   : m (InteractiveTImpl Q A E m α) → InteractiveTImpl Q A E m α

private unsafe def elimImpl {m : Type u → Type u} [Monad m] (x : InteractiveTImpl Q A E m α)
    (hPure : α → m β) (hInter : Q → (A → InteractiveTImpl Q A E m α) → m β) (hError : E → m β) : m β :=
  match x with
  | .pure a          => hPure a
  | .interact q cont => hInter q cont
  | .throw e         => hError e
  | .squash x        => do elimImpl (← x) hPure hInter hError

@[inline] private unsafe def specImpl (Q A E : Type u) (m : Type u → Type u) : Spec Q A E m where
  interactM := InteractiveTImpl Q A E m
  pure      := .pure
  interact  := .interact
  throw     := .throw
  squash    := .squash
  elim      := elimImpl

@[implemented_by specImpl]
private opaque spec (Q A E : Type u) (m : Type u → Type u) : Spec Q A E m

end InteractiveT

def InteractiveT (Q A E : Type u) (m : Type u → Type u) : Type u → Type u :=
  (InteractiveT.spec Q A E m).interactM

namespace InteractiveT

variable {Q A E : Type u} {m : Type u → Type u} [Inhabited E] [Monad m]

@[inline] def pure : α → InteractiveT Q A E m α :=
  (InteractiveT.spec Q A E m).pure

@[inline] def interact : Q → (A → InteractiveT Q A E m α) → InteractiveT Q A E m α :=
  (InteractiveT.spec Q A E m).interact

@[inline] def throw : E → InteractiveT Q A E m α :=
  (InteractiveT.spec Q A E m).throw

@[inline] def squash : m (InteractiveT Q A E m α) → InteractiveT Q A E m α :=
  (InteractiveT.spec Q A E m).squash

@[inline] def elim : InteractiveT Q A E m α →
    (output : α → m β) →
    (continuation : Q → (A → InteractiveT Q A E m α) → m β) →
    (error : E → m β) → m β :=
  (InteractiveT.spec Q A E m).elim

instance : Inhabited (InteractiveT Q A E m α) := ⟨throw default⟩


def askQuestion (q : Q) : InteractiveT Q A E m A := interact q pure

def giveAnswer (a : A) (x : InteractiveT Q A E m α) : OptionT m (InteractiveT Q A E m α) :=
  x.elim
    fun _      => return none
    fun _ cont => return some (cont a)
    fun _      => return none

def runWithAnswers (as : Array A) (x : InteractiveT Q A E m α) : OptionT m α := do
  let x ← as.foldlM (fun x a => giveAnswer a x) x
  x.elim
    fun x   => return some x
    fun _ _ => return none
    fun _   => return none

private partial def bind (x : InteractiveT Q A E m α) (f : α → InteractiveT Q A E m β) : InteractiveT Q A E m β :=
  squash do
    x.elim
      fun a      => return f a
      fun q cont => return interact q fun ans => bind (cont ans) f
      fun e      => return throw e

private partial def InteractiveT.tryCatch (x : InteractiveT Q A E m α) (handle : E → InteractiveT Q A E m α) : (InteractiveT Q A E m α) :=
  squash do
    x.elim
      fun a      => return pure a
      fun q cont => return interact q fun answer => tryCatch (cont answer) handle
      fun e      => return handle e

instance : Monad (InteractiveT Q A E m) where
  pure := InteractiveT.pure
  bind := InteractiveT.bind

instance : MonadLift m (InteractiveT Q A E m) where
  monadLift x := squash do return InteractiveT.pure (← x)

instance : MonadExcept E (InteractiveT Q A E m) where
  throw := InteractiveT.throw
  tryCatch := InteractiveT.tryCatch

end InteractiveT

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
    | "error" => do
      let data ← json.getObjVal? "data"
      let data : WithRpcRef MessageData ← rpcDecode data
      return .error data
    | _ => .error s!"Invalid kind: {kind}"

abbrev InteractiveM := InteractiveT UserQuestion Json Exception IO

def throwWidgetError (e : String) : InteractiveM α :=
  .squash (throw (IO.userError e))


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

def askUser : UserQuestion → InteractiveM Json := InteractiveT.askQuestion

def askUserForm (form : Html) : InteractiveM Json := do
  let .element "form" _ elems := form | throwWidgetError "Not an Html form"
  askUser (.form elems)
open ProofWidgets.Jsx in
def askUserInput (title input : Html) : InteractiveM String := do
  let .element "input" inputAttrs inputElems := input | throwWidgetError "Not an Html input"
  let inputAttrs := inputAttrs.push ("name", "query")
  let input := Html.element "input" inputAttrs inputElems
  let submit := <input type="submit"/>
  let answer ← askUser (.form #[title, input, submit])
  match answer.getObjValAs? String "query" with
  | .error err => throwWidgetError err
  | .ok answer => return answer

def askUserString (question : Html) : InteractiveM String :=
  askUserInput question <input type="string"/>
def askUserInt (question : Html) : InteractiveM Int := do
  let answer ← askUserInput question <input type="number" defaultValue="0"/>
  let some answer := answer.toInt? | throwWidgetError "not an integer"
  return answer
def askUserSelect {α : Type} (question : Html) (options : List (α × Html))
  : InteractiveM α := do
  match fromJson? (← askUser (.select question (options.map Prod.snd).toArray)) with
  | .error err => throwWidgetError err
  | .ok (answer : Nat) => do
    let some (answer,_) := options.get? answer | throwWidgetError "Index out of bounds"
    return answer
def askUserBool (question : Html) : InteractiveM Bool
  := askUserSelect question [
    (true, <button>Yes</button>),
    (false, <button>No</button>)
  ]
def askUserConfirm (message : Html) : InteractiveM Unit
  := askUserSelect message [((), <button>OK</button>)]

--   __        ___     _            _
--   \ \      / (_) __| | __ _  ___| |_
--    \ \ /\ / /| |/ _` |/ _` |/ _ \ __|
--     \ V  V / | | (_| | (_| |  __/ |_
--      \_/\_/  |_|\__,_|\__, |\___|\__|
--                       |___/

initialize continuationRef : IO.Ref (Json → InteractiveM Unit) ← IO.mkRef default

def runWidget (x : InteractiveM Unit) : IO UserQuestion :=
  try
    x.elim
      fun _ => do
        continuationRef.set (fun _ => pure ())
        return .empty
      fun q cont => do
        continuationRef.set cont
        return q
      fun e => do
        continuationRef.set (fun _ => pure ())
        return .error <| WithRpcRef.mk e.toMessageData
  catch e =>
    continuationRef.set (fun _ => pure ())
    return .select <p><b>Widget Error: </b>{.text e.toString}</p> #[<button>OK</button>]

def InteractiveMUnit := InteractiveM Unit
deriving instance TypeName for InteractiveMUnit

instance : RpcEncodable (InteractiveM Unit) where
  rpcEncode x := rpcEncode (⟨x⟩ : WithRpcRef InteractiveMUnit)
  rpcDecode json := do
    let out : WithRpcRef InteractiveMUnit ← rpcDecode json
    return out.val

structure initArgs where
  code : InteractiveM Unit
deriving RpcEncodable

@[server_rpc_method]
def initializeInteraction (args : initArgs) : RequestM (RequestTask UserQuestion) :=
  RequestM.asTask do
    runWidget args.code

@[server_rpc_method]
def processUserAnswer (answer : Json) : RequestM (RequestTask UserQuestion) :=
  RequestM.asTask do
    let continuation ← continuationRef.get
    runWidget (continuation answer)


--    _____          _   _      ___ __  __
--   |_   _|_ _  ___| |_(_) ___|_ _|  \/  |
--     | |/ _` |/ __| __| |/ __|| || |\/| |
--     | | (_| | (__| |_| | (__ | || |  | |
--     |_|\__,_|\___|\__|_|\___|___|_|  |_|
--

open Elab Tactic

abbrev CoreIM     := ReaderT Core.Context <| StateRefT Core.State InteractiveM
abbrev MetaIM     := ReaderT Meta.Context <| StateRefT Meta.State CoreIM
abbrev TermElabIM := ReaderT Term.Context <| StateRefT Term.State MetaIM
abbrev TacticIM   := ReaderT Tactic.Context <| StateRefT Tactic.State TermElabIM

instance : MonadLift (EIO Exception) InteractiveM where
  monadLift x := InteractiveT.squash fun world =>
    match x world with
    | .ok    a world => .ok (pure a) world
    | .error e world => .ok (throw e) world

private def liftReaderState [MonadLift m n] : MonadLift (ReaderT ρ (StateRefT' ω σ m)) (ReaderT ρ (StateRefT' ω σ n)) where
  monadLift x := fun c s => liftM (x c s)

instance : MonadLift CoreM CoreIM := liftReaderState
instance : MonadLift MetaM MetaIM := liftReaderState
instance : MonadLift TermElabM TermElabIM := liftReaderState
instance : MonadLift TacticM TacticIM := liftReaderState

def separateReaderState
  {ρ ω σ: Type} (im m : Type → Type)
  (finalize : ∀ {α}, im α → m (InteractiveM α) )
  [Monad im] [Monad m] [MonadLiftT (ST ω) im] [MonadLiftT (ST ω) m]
  {α : Type}
  (code : ReaderT ρ (StateRefT' ω σ im) α)
: ReaderT ρ (StateRefT' ω σ m) (InteractiveM α) := do
  let ctx ← read
  let state : σ ← liftM (m := StateRefT' ω σ m) get
  finalize ((code.run ctx).run' state)

def CoreIM.splitIM {α : Type} : CoreIM α → CoreM (InteractiveM α)
  := separateReaderState InteractiveM (EIO Exception) (λ x ↦ return x)
def MetaIM.splitIM {α : Type} : MetaIM α → MetaM (InteractiveM α)
  := separateReaderState _ _ CoreIM.splitIM
def TermElabIM.splitIM {α : Type} : TermElabIM α → TermElabM (InteractiveM α)
  := separateReaderState _ _ MetaIM.splitIM
def TacticIM.splitIM {α : Type} : TacticIM α → TacticM (InteractiveM α)
  := separateReaderState _ _ TermElabIM.splitIM
