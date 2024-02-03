import Lean
import ProofWidgets
import Mathlib.Tactic

open ProofWidgets.Jsx
open Lean ProofWidgets Server

namespace InteractiveT

private structure Spec (Q A : Type u) (m : Type u → Type u) where
  interactM : Type u → Type u
  pure      : α → interactM α
  interact  : Q → (A → (interactM α)) → interactM α
  squash    : m (interactM α) → interactM α
  elim      : [Inhabited Q] → [Monad m] → interactM α → (α → m β) → (Q → (A → interactM α) → m β) → m β
  inhabited : [Inhabited Q] → Inhabited (interactM α)

instance : Inhabited (Spec Q A m) where
  default := {
    interactM := fun _ => PUnit
    pure := fun _ => ⟨⟩
    interact := fun _ _ => ⟨⟩
    squash := fun _ => ⟨⟩
    elim := fun _ _ f => f default (fun _ => ⟨⟩)
    inhabited := ⟨⟨⟩⟩
  }

private unsafe inductive InteractiveTImpl (Q A : Type u) (m : Type u → Type u) (α : Type u)
  | pure : α → InteractiveTImpl Q A m α
  | squash : m (InteractiveTImpl Q A m α) → InteractiveTImpl Q A m α
  | interact : Q → (A → InteractiveTImpl Q A m α) → InteractiveTImpl Q A m α

private unsafe def elimImpl {m : Type u → Type u} [Monad m] (x : InteractiveTImpl Q A m α)
    (hPure : α → m β) (hInter : Q → (A → InteractiveTImpl Q A m α) → m β) : m β :=
  match x with
  | .pure a => hPure a
  | .squash x => do elimImpl (← x) hPure hInter
  | .interact q cont => hInter q cont

private unsafe def inhabitedImpl [Inhabited Q] : InteractiveTImpl Q A m α :=
  .interact default fun _ => inhabitedImpl

@[inline] private unsafe def specImpl (Q A : Type u) (m : Type u → Type u) : Spec Q A m where
  interactM := InteractiveTImpl Q A m
  pure := .pure
  interact := .interact
  squash := .squash
  elim := elimImpl
  inhabited := ⟨inhabitedImpl⟩

@[implemented_by specImpl]
private opaque spec (Q A : Type u) (m : Type u → Type u) : Spec Q A m

end InteractiveT

def InteractiveT (Q A : Type u) (m : Type u → Type u) : Type u → Type u :=
  (InteractiveT.spec Q A m).interactM

namespace InteractiveT

variable {Q A : Type u} {m : Type u → Type u} [Inhabited Q] [Monad m]

@[inline] def pure : α → InteractiveT Q A m α :=
  (InteractiveT.spec Q A m).pure

@[inline] def interact : Q → (A → InteractiveT Q A m α) → InteractiveT Q A m α :=
  (InteractiveT.spec Q A m).interact

@[inline] def squash : m (InteractiveT Q A m α) → InteractiveT Q A m α :=
  (InteractiveT.spec Q A m).squash

@[inline] def elim : InteractiveT Q A m α → (α → m β) → (Q → (A → InteractiveT Q A m α) → m β) → m β :=
  (InteractiveT.spec Q A m).elim

instance : Inhabited (InteractiveT Q A m α) :=
  (InteractiveT.spec Q A m).inhabited


def askQuestion (q : Q) : InteractiveT Q A m A := interact q pure

def giveAnswer (a : A) (x : InteractiveT Q A m α) : OptionT m (InteractiveT Q A m α) :=
  x.elim
    (fun _ => return none)
    (fun _ cont => return some (cont a))

def runWithAnswers (as : Array A) (x : InteractiveT Q A m α) : OptionT m α := do
  let x ← as.foldlM (fun x a => giveAnswer a x) x
  x.elim
    (fun x => return some x)
    (fun _ _ => return none)

private partial def bind (x : InteractiveT Q A m α) (f : α → InteractiveT Q A m β) : InteractiveT Q A m β :=
  squash do
    x.elim
      (fun a => return f a)
      (fun q cont => return interact q fun ans => bind (cont ans) f)

private partial def InteractiveT.tryCatch [MonadExcept ε m] (x : InteractiveT Q A m α) (handle : ε → InteractiveT Q A m α) : (InteractiveT Q A m α) :=
  squash do
  try
    x.elim
      (fun a => return pure a)
      (fun q cont =>
        return interact q fun answer => tryCatch (cont answer) handle)
  catch e =>
    return handle e

instance : Monad (InteractiveT Q A m) where
  pure := InteractiveT.pure
  bind := InteractiveT.bind

instance : MonadLift m (InteractiveT Q A m) where
  monadLift x := squash do return pure (← x)

instance [MonadExcept ε m] : MonadExcept ε (InteractiveT Q A m) where
  throw e := .squash (throw e)
  tryCatch := InteractiveT.tryCatch

end InteractiveT

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
      let elems : Array Html ← elems.mapM rpcDecode
      return .form elems
    | "select" =>
      let question ← json.getObjVal? "question"
      let question : Html ← rpcDecode question
      let options ← json.getObjVal? "options"
      let options ← options.getArr?
      let options : Array Html ← options.mapM rpcDecode
      return .select question options
    | _ => .error s!"Invalid kind: {kind}"

abbrev InteractiveM := InteractiveT UserQuestion Json IO

-- Reference / Widget

initialize continuationRef : IO.Ref (Json → InteractiveM Unit) ← IO.mkRef default

def runWidget (x : InteractiveM Unit) : IO UserQuestion :=
  x.elim
    (fun _ => do
      continuationRef.set (fun _ => pure ())
      return .empty)
    (fun q cont => do
      continuationRef.set cont
      return q)

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
    liftM (runWidget args.code)
@[server_rpc_method]
def processUserAnswer (answer : Json) : RequestM (RequestTask UserQuestion) :=
  RequestM.asTask do
    let continuation ← continuationRef.get
    runWidget (continuation answer)

-- Specific Questions

def askUser : UserQuestion → InteractiveM Json := InteractiveT.askQuestion

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
