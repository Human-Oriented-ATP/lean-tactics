import Lean
import ProofWidgets
import Mathlib.Tactic

open ProofWidgets.Jsx
open Lean ProofWidgets Server

namespace Interactive

variable (m : Type → Type) (Q A E : Type) [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A]

structure Spec [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A] where
  InteractiveOutput : Type → Type
  instMonad : Monad (m ∘ InteractiveOutput)
  instMonadExcept : MonadExcept E (m ∘ InteractiveOutput)
  terminate {α : Type} (out : α) : InteractiveOutput α
  interact {α : Type} (question : Q) (continuation : A → m (InteractiveOutput α)) : InteractiveOutput α
  cases {α : Type} {out : Type}
    (t : InteractiveOutput α)
    (terminate : α → out)
    (interact : (question : Q) → (continuation : A → m (InteractiveOutput α)) → out)
    : out

instance (m : Type _ → Type _) [Monad m] : Monad (m ∘ m) where
  pure a := show m (m _) from do
    return return a
  bind a f := show m (m _) from do
    (← a) >>= f

instance (m : Type _ → Type _) [Monad m] [MonadExcept ε m] : MonadExcept ε (m ∘ m) where
  throw err := show m (m _) from do
    return throw err
  tryCatch t c := show m (m _) from do
    try
      t
    catch e =>
      c e

instance : Inhabited (Spec m Q A E) where
  default := {
    InteractiveOutput := m
    instMonad := inferInstance
    instMonadExcept := inferInstance
    terminate := λ out => pure out
    interact := fun _ c => Monad.join (c default)
    cases := λ α {out} t m question ↦ question default (λ _ ↦ pure t)
  }

unsafe inductive InteractiveOutput' (Q A : Type) (m : Type → Type) (α : Type) where
  | terminate (out : α)
  | interact (question : Q) (continuation : A → m (InteractiveOutput' Q A m α))

unsafe abbrev InteractiveT (Q A : Type) (m : Type → Type) := m ∘ (InteractiveOutput' Q A m)

unsafe def InteractiveT.pure (a : α) : InteractiveT Q A m α :=
  Pure.pure (f := m) (InteractiveOutput'.terminate a)

unsafe def InteractiveT.bind (code : InteractiveT Q A m α) (f : α → InteractiveT Q A m β) : InteractiveT Q A m β := show m (InteractiveOutput' Q A m _) from do
  match ← code with
    | .terminate a => f a
    | .interact question continuation =>
      return .interact question <| fun a ↦ do
        (bind (continuation a) f)

private
unsafe def InteractiveT.tryCatch {α : Type} (t : InteractiveT Q A m α) (c : E → InteractiveT Q A m α)
: (InteractiveT Q A m α) := show m _ from do
  try
    let out ← t
    match out with
    | .terminate _ => return out
    | .interact question continuation =>
      return .interact question fun answer =>
        InteractiveT.tryCatch (continuation answer) c
  catch e =>
    c e

unsafe instance : Monad (InteractiveT Q A m) where
  pure := InteractiveT.pure m Q A
  bind := InteractiveT.bind m Q A

unsafe instance : MonadExcept E (InteractiveT Q A m) where
  throw e := throw (m := m) e
  tryCatch t c := tryCatch (m := m) t c

private unsafe def specImpl (m : Type → Type) (Q A E : Type) [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A] : Spec m Q A E where
  InteractiveOutput := InteractiveOutput' Q A m
  instMonad := inferInstanceAs (Monad <| InteractiveT Q A m)
  instMonadExcept := inferInstanceAs (MonadExcept E <| InteractiveT Q A m)
  terminate := InteractiveOutput'.terminate
  interact := InteractiveOutput'.interact
  cases t terminate interact := match t with
  | .terminate a => terminate a
  | .interact q c => interact q c

@[implemented_by specImpl]
private opaque spec (m : Type → Type) (Q A E : Type) [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A] : Spec m Q A E

end Interactive

def InteractiveT (m : Type → Type) (Q A E : Type)
  [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A]
  : Type → Type
  := (λ α ↦ m ((Interactive.spec m Q A E).InteractiveOutput α))

def InteractiveT.core {m : Type → Type} {Q A E : Type} [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A] {α : Type}
  : (InteractiveT m Q A E α) → m ((Interactive.spec m Q A E).InteractiveOutput α) := id
def InteractiveT.asCore {m : Type → Type} {Q A E : Type} [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A] {α : Type}
  : m ((Interactive.spec m Q A E).InteractiveOutput α) → (InteractiveT m Q A E α) := id

instance (m : Type → Type) (Q A E : Type) [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A]
  : Monad (InteractiveT m Q A E) := (Interactive.spec m Q A E).instMonad

instance (m : Type → Type) (Q A E : Type) [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A]
  : MonadExcept E (InteractiveT m Q A E) := (Interactive.spec m Q A E).instMonadExcept

instance (m : Type → Type) (Q A E : Type) [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A] : MonadLift m (InteractiveT m Q A E) where
   monadLift {α : Type} (im : m α) : m ((Interactive.spec m Q A E).InteractiveOutput α) := do
    let out ← im
    return (Interactive.Spec.terminate _ out)

unsafe def runPair {m : Type → Type} {Q A E α : Type} [Monad m] [MonadExcept E m] [Inhabited Q] [Inhabited A]
  (agent1 : InteractiveT m Q A E α) (agent2 : Q → InteractiveT m A Q E α)
  : m α := do
  (Interactive.spec m Q A E).cases (← agent1)
    ( λ out2 ↦ return out2 )
    ( λ question continuation ↦
      runPair (agent2 question) continuation )

-- Question / Answer instance

inductive UserQuestion : Type where
| empty
| form (elems : Array Html)
| select (question : Html) (array : Array Html)
instance UserQuestion.Inhabited : Inhabited UserQuestion where
  default := .empty

instance : RpcEncodable UserQuestion where
  rpcEncode q := match q with
  | .empty => return Json.mkObj [("kind", "empty")]
  | .form elems => do
    let elems ← elems.mapM (λ elem ↦ rpcEncode elem)
    return Json.mkObj [("kind", "form"), ("elems", Json.arr elems)]
  | .select question options => do
    let question ← rpcEncode question
    let options ← options.mapM rpcEncode
    return Json.mkObj [("kind", "select"), ("question",question),
    ("options", Json.arr options)]
  rpcDecode json := do
    let kind ← json.getObjVal? "kind"
    let kind ← kind.getStr?
    match kind with
    | "empty" =>
      return .empty
    | "form" => do
      let elems ← json.getObjVal? "elems"
      let elems ← elems.getArr?
      let elems : Array Html ← elems.mapM (λ elem ↦ rpcDecode elem)
      return .form elems
    | "select" =>
      let question ← json.getObjVal? "question"
      let question : Html ← rpcDecode question
      let options ← json.getObjVal? "options"
      let options ← options.getArr?
      let options : Array Html ← options.mapM rpcDecode
      return .select question options
    | _ => .error s!"Invalid kind: {kind}"

#check Json.getObjVal?

def InteractiveM := InteractiveT IO UserQuestion Json IO.Error
deriving Monad, MonadExcept

instance : MonadLift IO InteractiveM where
  monadLift {α : Type} := (monadLift : IO α → InteractiveT IO UserQuestion Json IO.Error α)

-- Reference / Widget

initialize continuationRef : IO.Ref (Json → InteractiveM Unit) ← IO.mkRef default

def runWidget (m : InteractiveM Unit) : IO UserQuestion := do
  (Interactive.spec _ _ _ _).cases (← m)
    ( λ out ↦ do
      continuationRef.set (λ _ ↦ return default)
      return default )
    ( λ question continuation ↦ do
      continuationRef.set (λ answer ↦ (continuation answer))
      return question )

def InteractiveMUnit := InteractiveM Unit
deriving instance TypeName for InteractiveMUnit

instance : RpcEncodable (InteractiveM Unit) where
  rpcEncode x := rpcEncode (WithRpcRef.mk x : WithRpcRef InteractiveMUnit)
  rpcDecode json := do
    let out : WithRpcRef InteractiveMUnit ← rpcDecode json
    return out.val

structure initArgs where
  code : InteractiveM Unit
deriving RpcEncodable

@[server_rpc_method]
def initializeInteraction (args : initArgs) : RequestM (RequestTask UserQuestion) := do
  RequestM.asTask do
    liftM (runWidget args.code)
@[server_rpc_method]
def processUserAnswer (answer : Json) : RequestM (RequestTask UserQuestion) := do
  RequestM.asTask do
    let continuation ← continuationRef.get
    runWidget (continuation answer)

-- Specific Questions

def askUser (question : UserQuestion) : InteractiveM Json := InteractiveT.asCore do
  return ((Interactive.spec _ _ _ _).interact question (λ answer ↦
    return ((Interactive.spec _ _ _ _).terminate answer)))

def askUserForm (form : Html) : InteractiveM Json := do
  let .element "form" _ elems := form | throw <| IO.userError "Not an Html form"
  askUser (.form elems)
open ProofWidgets.Jsx in
def askUserInput (title input : Html) : InteractiveM String := do
  let .element "input" inputAttrs inputElems := input | throw <| IO.userError "Not an Html input"
  let inputAttrs := inputAttrs.push ("name", "query")
  let input := Html.element "input" inputAttrs inputElems
  let submit := <input type="submit"/>
  let answer ← askUser (.form #[title, input, submit])
  match answer.getObjValAs? String "query" with
  | .error err => throw <| IO.userError err
  | .ok answer => return answer

def askUserString (question : Html) : InteractiveM String :=
  askUserInput question <input type="string"/>
def askUserInt (question : Html) : InteractiveM Int := do
  let answer ← askUserInput question <input type="number" defaultValue="0"/>
  let some answer := answer.toInt? | throw <| IO.userError "not an integer"
  return answer
def askUserSelect {α : Type} (question : Html) (options : List (α × Html))
  : InteractiveM α := do
  match fromJson? (← askUser (.select question (options.map Prod.snd).toArray)) with
  | .error err => throw <| IO.userError err
  | .ok (answer : Nat) => do
    let some (answer,_) := options.get? answer
      | throw (IO.userError "Index out of bounds")
    return answer
def askUserBool (question : Html) : InteractiveM Bool
  := askUserSelect question [
    (true, <button>Yes</button>),
    (false, <button>No</button>)
  ]
def askUserConfirm (message : Html) : InteractiveM Unit
  := askUserSelect message [((), <button>OK</button>)]
