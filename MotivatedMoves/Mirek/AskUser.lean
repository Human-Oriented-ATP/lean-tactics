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

inductive Interaction (Q A α : Type u)
  | terminate : α → Interaction Q A α
  | interact  : Q → (A → Interaction Q A α) → Interaction Q A α

namespace Interaction

variable {α β Q A : Type u}

@[always_inline, inline]
protected def bind (x : Interaction Q A α) (f : α → Interaction Q A β) : Interaction Q A β :=
  match x with
  | terminate a => f a
  | interact q cont => interact q (fun ans => Interaction.bind (cont ans) f)

@[always_inline]
instance : Monad (Interaction Q A) where
  pure     := terminate
  bind     := Interaction.bind


def askQuestion (q : Q) : Interaction Q A A := interact q terminate

def giveAnswer (a : A) (x : Interaction Q A α) : Option (Interaction Q A α) :=
  match x with
  | .interact _ cont => (cont a)
  | _ => none

def runWithAnswers (as : Array A) (x : Interaction Q A α) : Option α := do
  match ← as.foldlM (fun x a => giveAnswer a x) x with
  | terminate x => some x
  | _ => none

end Interaction

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

abbrev InteractiveM := ExceptT (Exception ⊕ String) $ Interaction UserQuestion Json

def throwWidgetError (e : String) : InteractiveM α := throw (.inr e)


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

def askUser (q : UserQuestion) : InteractiveM Json := liftM (Interaction.askQuestion q)

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

def runWidget (x : InteractiveM Unit) : IO UserQuestion := do
  match x with
  | .interact q cont =>
    continuationRef.set cont
    return q

  | .terminate (.ok ()) =>
    continuationRef.set (fun _ => pure ())
    return .empty

  | .terminate (.error (.inl e)) =>
    continuationRef.set (fun _ => pure ())
    return .error <| WithRpcRef.mk e.toMessageData

  | .terminate (.error (.inr e)) =>
    continuationRef.set (fun _ => pure ())
    return .select <p><b>Widget Error: </b>{.text e}</p> #[<button>OK</button>]

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


abbrev IIO := ReaderT IO.RealWorld InteractiveM

instance : STWorld IO.RealWorld IIO where

instance : MonadLift (EIO Exception) IIO where
  monadLift x := fun s => do
    match x s with
    | .ok x _ => return x
    | .error e _ => throw (.inl e)


open Elab Tactic

abbrev CoreIM     := ReaderT Core.Context <| StateRefT Core.State IIO
abbrev MetaIM     := ReaderT Meta.Context <| StateRefT Meta.State CoreIM
abbrev TermElabIM := ReaderT Term.Context <| StateRefT Term.State MetaIM
abbrev TacticIM   := ReaderT Tactic.Context <| StateRefT Tactic.State TermElabIM

variable [Monad n] [Monad m] [MonadLiftT (ST ω) m] [MonadLiftT (ST ω) n]

private def liftReaderState [MonadLift m n] : MonadLift (ReaderT ρ (StateRefT' ω σ m)) (ReaderT ρ (StateRefT' ω σ n)) where
  monadLift x := fun c => do liftM ((x c).run' (← get))

instance : MonadLift CoreM CoreIM := liftReaderState
instance : MonadLift MetaM MetaIM := liftReaderState
instance : MonadLift TermElabM TermElabIM := liftReaderState
instance : MonadLift TacticM TacticIM := liftReaderState

private def separateReaderState  (finalize : m α → n (InteractiveM α)) (x : ReaderT ρ (StateRefT' ω σ m) α) : ReaderT ρ (StateRefT' ω σ n) (InteractiveM α) :=
  fun c => do finalize ((x c).run' (← get))

def IIO.run : IIO α → EIO Exception (InteractiveM α) := fun x s => .ok (x s) s

def CoreIM.run     : CoreIM α     → CoreM     (InteractiveM α) := separateReaderState IIO.run
def MetaIM.run     : MetaIM α     → MetaM     (InteractiveM α) := separateReaderState CoreIM.run
def TermElabIM.run : TermElabIM α → TermElabM (InteractiveM α) := separateReaderState MetaIM.run
def TacticIM.run   : TacticIM α   → TacticM   (InteractiveM α) := separateReaderState TermElabIM.run
