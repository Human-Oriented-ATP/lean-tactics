import Lean
import ProofWidgets
import Mathlib.Tactic

open ProofWidgets.Jsx
open Lean ProofWidgets Server

-- Monad
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

-- Question instance
--     ___                  _   _               _           _
--    / _ \ _   _  ___  ___| |_(_) ___  _ __   (_)_ __  ___| |_ __ _ _ __   ___ ___
--   | | | | | | |/ _ \/ __| __| |/ _ \| '_ \  | | '_ \/ __| __/ _` | '_ \ / __/ _ \
--   | |_| | |_| |  __/\__ \ |_| | (_) | | | | | | | | \__ \ || (_| | | | | (_|  __/
--    \__\_\\__,_|\___||___/\__|_|\___/|_| |_| |_|_| |_|___/\__\__,_|_| |_|\___\___|
--

inductive QueryWidget : Type where
| widget (level : Int) (w : Html)
| initEdit (ident : Lsp.VersionedTextDocumentIdentifier) (startPos : Lsp.Position)
| insertLine (line : String)
deriving RpcEncodable
instance : Inhabited QueryWidget where
  default := .widget 0 <div/>

abbrev InteractiveM := ReaderT RequestContext <| IStateM QueryWidget Json (Exception ⊕ String) IO.RealWorld

def throwWidgetError (e : String) : InteractiveM α := throw (.inr e)

-- Display Widget
--    ____  _           _              __        ___     _            _
--   |  _ \(_)___ _ __ | | __ _ _   _  \ \      / (_) __| | __ _  ___| |_
--   | | | | / __| '_ \| |/ _` | | | |  \ \ /\ / /| |/ _` |/ _` |/ _ \ __|
--   | |_| | \__ \ |_) | | (_| | |_| |   \ V  V / | | (_| | (_| |  __/ |_
--   |____/|_|___/ .__/|_|\__,_|\__, |    \_/\_/  |_|\__,_|\__, |\___|\__|
--               |_|            |___/                      |___/

def ProgWidget.jscode := include_str ".." / ".." / "build" / "js" / "userQuery.js"

--  RpcEncodable by reference

def InteractiveMUnit := InteractiveM Unit
deriving instance TypeName for InteractiveMUnit
instance : RpcEncodable (InteractiveM Unit) where
  rpcEncode x := rpcEncode (⟨x⟩ : WithRpcRef InteractiveMUnit)
  rpcDecode json := do
    let out : WithRpcRef InteractiveMUnit ← rpcDecode json
    return out.val

def JsonToInteractiveMUnit := Json → InteractiveM Unit
deriving instance TypeName for JsonToInteractiveMUnit

structure ProgWidget.Props where
  code : InteractiveM Unit
deriving Server.RpcEncodable

@[widget_module]
def ProgWidget : Component ProgWidget.Props where
  javascript := ProgWidget.jscode

structure ProgWidget.Form.Props where
  elems : Array Html
deriving Server.RpcEncodable
@[widget_module]
def ProgWidget.Form : Component ProgWidget.Form.Props where
  javascript := ProgWidget.jscode
  «export» := "FormWidget"

structure ProgWidget.Select.Props where
  question : Html
  options : Array Html
deriving Server.RpcEncodable
@[widget_module]
def ProgWidget.Select : Component ProgWidget.Select.Props where
  javascript := ProgWidget.jscode
  «export» := "SelectWidget"

structure InteractiveMessageDataProps where
  msg : WithRpcRef MessageData
deriving RpcEncodable
@[widget_module]
def InteractiveMessageData : Component InteractiveMessageDataProps where
  javascript :=
   "import * as React from 'react';
    import { InteractiveMessageData } from '@leanprover/infoview';
    export default InteractiveMessageData;"

-- Specific questions
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

def queryWidget (q : QueryWidget) : InteractiveM Json := fun _ => IStateM.askQuestion q
def askWidget (lev : Int) (widget : Html) : InteractiveM Json := queryWidget (.widget lev widget)

def askUserForm (lev : Int) (form : Html) : InteractiveM Json := do
  let .element "form" _ elems := form | throwWidgetError "Not an Html form"
  askWidget lev <ProgWidget.Form elems={elems}/>
open ProofWidgets.Jsx in
def askUserInput (lev : Int) (title input : Html) : InteractiveM String := do
  let .element "input" inputAttrs inputElems := input | throwWidgetError "Not an Html input"
  let inputAttrs := inputAttrs.push ("name", "query")
  let input := Html.element "input" inputAttrs inputElems
  let submit := <input type="submit"/>
  let answer ← askWidget lev <ProgWidget.Form elems={#[title, input, submit]}/>
  match answer.getObjValAs? String "query" with
  | .error err => throwWidgetError err
  | .ok answer => return answer

def askUserString (lev : Int) (question : Html) : InteractiveM String :=
  askUserInput lev question <input type="string"/>
def askUserInt (lev : Int) (question : Html) : InteractiveM Int := do
  let answer ← askUserInput lev question <input type="number" defaultValue="0"/>
  let some answer := answer.toInt? | throwWidgetError "not an integer"
  return answer
def askUserSelect {α : Type} (lev : Int) (question : Html) (options : List (α × Html))
  : InteractiveM α := do
  let widget := <ProgWidget.Select question={question} options={(options.map Prod.snd).toArray}/>
  let answer ← askWidget lev widget
  match fromJson? answer with
  | .error err => throwWidgetError (toString answer) -- err
  | .ok (answer : Nat) => do
    let some (answer,_) := options.get? answer | throwWidgetError "Index out of bounds"
    return answer
def askUserBool (lev : Int) (question : Html) : InteractiveM Bool
  := askUserSelect lev question [
    (true, <button>Yes</button>),
    (false, <button>No</button>)
  ]
def askUserConfirm (lev : Int) (message : Html) : InteractiveM Unit
  := askUserSelect lev message [((), <button>OK</button>)]

def initEdit (pos : Lsp.Position) : InteractiveM Unit := do
  let ctx : RequestContext ← read
  let meta := ctx.doc.meta
  let ident : Lsp.VersionedTextDocumentIdentifier := {
    uri := meta.uri,
    version? := meta.version,
  }
  _ ← queryWidget (.initEdit ident pos)

def insertLine (line : String) : InteractiveM Unit := do
  _ ← queryWidget (.insertLine line)
  return

-- Process Widget
--    ____                               __        ___     _            _
--   |  _ \ _ __ ___   ___ ___  ___ ___  \ \      / (_) __| | __ _  ___| |_
--   | |_) | '__/ _ \ / __/ _ \/ __/ __|  \ \ /\ / /| |/ _` |/ _` |/ _ \ __|
--   |  __/| | | (_) | (_|  __/\__ \__ \   \ V  V / | | (_| | (_| |  __/ |_
--   |_|   |_|  \___/ \___\___||___/___/    \_/\_/  |_|\__,_|\__, |\___|\__|
--                                                           |___/

def runWidget (x : InteractiveM Unit) : RequestM (QueryWidget × (Json → InteractiveM Unit)) := fun ctx => do
  match x ctx (← EStateM.get) with
  | .interact q s cont =>
    EStateM.set s
    return (q, fun json _ => cont json)

  | .terminate () s =>
    EStateM.set s
    return (default, fun _ => pure ())

  | .throw (.inl e) s =>
    EStateM.set s
    return (
      .widget 0 <InteractiveMessageData msg={(WithRpcRef.mk e.toMessageData)}/>,
      fun _ => pure ()
    )

  | .throw (.inr e) s =>
    EStateM.set s
    return (.widget 0 <ProgWidget.Select
      question={<p><b>Widget Error: </b>{.text e}</p>}
      options={#[<button>OK</button>]} />,
      fun _ => pure ()
    )

@[server_rpc_method]
def initializeInteraction (code : InteractiveM Unit) : RequestM (RequestTask (QueryWidget × WithRpcRef JsonToInteractiveMUnit)) :=
  RequestM.asTask do
    let (question, cont) ← runWidget code
    return (question, WithRpcRef.mk cont)

@[server_rpc_method]
def processUserAnswer
  (args : Json × (WithRpcRef JsonToInteractiveMUnit))
  : RequestM (RequestTask (QueryWidget × (WithRpcRef JsonToInteractiveMUnit))) :=
  RequestM.asTask do
    let (answer, cont) := args
    let (question, cont2) ← runWidget (cont.val answer)
    return (question, WithRpcRef.mk cont2)

-- TacticIM
--    _____          _   _      ___ __  __
--   |_   _|_ _  ___| |_(_) ___|_ _|  \/  |
--     | |/ _` |/ __| __| |/ __|| || |\/| |
--     | | (_| | (__| |_| | (__ | || |  | |
--     |_|\__,_|\___|\__|_|\___|___|_|  |_|
--

instance : STWorld IO.RealWorld InteractiveM where

instance : MonadLift (EIO Exception) InteractiveM where
  monadLift x := fun _ s =>
    match x s with
    | .ok x s => .terminate x s
    | .error e s => .throw (.inl e) s

open Elab Tactic

abbrev CoreIM     := ReaderT Core.Context <| StateRefT Core.State InteractiveM
abbrev MetaIM     := ReaderT Meta.Context <| StateRefT Meta.State CoreIM
abbrev TermElabIM := ReaderT Term.Context <| StateRefT Term.State MetaIM
abbrev TacticIM   := ReaderT Tactic.Context <| StateRefT Tactic.State TermElabIM

section

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

private def separateReaderState (finalize : m α → n (InteractiveM α)) (x : ReaderT ρ (StateRefT' ω σ m) α)
    : ReaderT ρ (StateRefT' ω σ n) (InteractiveM α) :=
  fun c => do finalize ((x c).run' (← get))

def CoreIM.run     : CoreIM α     → CoreM     (InteractiveM α) := separateReaderState pure
def MetaIM.run     : MetaIM α     → MetaM     (InteractiveM α) := separateReaderState CoreIM.run
def TermElabIM.run : TermElabIM α → TermElabM (InteractiveM α) := separateReaderState MetaIM.run
def TacticIM.run   : TacticIM α   → TacticM   (InteractiveM α) := separateReaderState TermElabIM.run

end

/-
This example shows that it is important to inline bind.

def g (n : Nat) : InteractiveM Nat := do
  for _ in [:n] do
    if true then
      continue
  return 4

#eval show TermElabM _ from do
  let x ← pure (g 1000000)
  let y := IStateM.runWithAnswersIO #[] x
  timeit "" y
-/

-- Demo
--    ____
--   |  _ \  ___ _ __ ___   ___
--   | | | |/ _ \ '_ ` _ \ / _ \
--   | |_| |  __/ | | | | | (_) |
--   |____/ \___|_| |_| |_|\___/
--

def tactic_code_step : TacticIM Unit := do
  let goal : Format ← Lean.Elab.Tactic.withMainContext do
    let goal ← Elab.Tactic.getMainGoal
    Elab.Term.ppGoal goal
  let tacStr ← askUserSelect 0 <p>{.text s!"The goal is {goal}"}</p> [
    ("rewrite [Nat.mul_comm]", <button>Rw Mul</button>),
    ("rewrite [Nat.add_comm]", <button>Rw Comm</button>),
  ]
  insertLine ("    "++tacStr)
  let .ok tacStx := Parser.runParserCategory (← getEnv) `tactic tacStr | throwWidgetError "failed to parse tactic"
  evalTactic tacStx
  -- TODO: ask user which tactic to apply, apply it, and insert line

partial def tactic_code : TacticIM Unit := do
  tactic_code_step
  tactic_code

syntax (name:=InteractiveTac) "interactive_tac" tacticSeq : tactic

@[tactic InteractiveTac]
def InteractiveTacImpl:Lean.Elab.Tactic.Tactic
| stx@`(tactic|interactive_tac $seq) => do
  let some ⟨stxStart, stxEnd⟩ := (←getFileMap).rangeOfStx? stx | return
  let current_code : TacticIM Unit := (do
    Lean.Elab.Tactic.evalTacticSeq seq
    initEdit stxEnd
    tactic_code
  )
  let raw_code ← current_code.run

  Widget.savePanelWidgetInfo (hash ProgWidget.javascript) (do
    let jsonCode ← rpcEncode raw_code
    return json%{
      code : $jsonCode
    }
  ) stx
| _ => Lean.Elab.throwUnsupportedSyntax

example (a b c d : Nat) (h : c+b*a = d) : a*b+c = d := by
  interactive_tac
    rewrite [Nat.add_comm]

#html <ProgWidget code={do
  let name ← askUserString 0 <p>What is your name?</p>
  let surname ← askUserString 1 <p>Hi {.text name}, what is your surname?</p>
  askUserConfirm 0 <p>{.text s!"Nice to meet you, {name} {surname}"}</p>
} />
#html <ProgWidget code={do
  let teletubie : String ← askUserSelect 0 <p>Favorite color?</p> [
    ("Tinky Winky", <button style={Json.mkObj [("background-color", "purple"), ("color", "white")]}>purple</button>),
    ("Dipsy", <button style={Json.mkObj [("background-color", "green"), ("color", "white")]}>green</button>),
    ("Laa-Laa", <button style={Json.mkObj [("background-color", "yellow")]}>yellow</button>),
    ("Po", <button style={Json.mkObj [("background-color", "red"), ("color", "white")]}>red</button>)
  ]
  let response ← askUserString 0 <p>{.text s!"OMG, how can you like the color of {teletubie}, the most annoying of all Teletubbies??"}</p>
  let i ← askUserInt 0 <p>{.text s!"What do you mean by '{response}'? Let's try something different. I am thinking of a number, try to guess it."}</p>
  let i ← askUserInt 0 <p>{.text s!"Oh, you thought {i}? That was close, I was thinking of {i+1}. Let's try again."}</p>
  throw $ .inl $ Exception.internal ⟨4⟩
  throwWidgetError "Sorry, I played with exceptions"
  let _ ← askUserInt 0 <p>{.text s!"Oh, you thought {i}? That was close, I was thinking of {i+1}. Let's try again."}</p>
} />
#html <ProgWidget code={do
  let ans ← askUserSelect 0 <div/> [
    ("You clicked a link", <div>Click <a>here</a></div>),
    ("You clicked a button", <div> or <button>here</button></div>),
  ]
  askUserConfirm 0 <| Html.text <| toString ans
  let ans ← askUserForm 0 <form>
    <p><label>Username: </label>
    <input name="str" type="string"/></p>
    <p><label>Password: </label>
    <input name="pass" type="password"/></p>
    <p><label>Age: </label>
    <input name="num" type="number"/></p>
    <input type="submit"/>
  </form>
  askUserConfirm 0 <| Html.text <| toString ans
  let ans ← askUserInput 0 <p>Now a <b>real </b> favorite color</p> <input type="color" defaultValue="#00ffff"/>
  askUserConfirm 0 <| <p>{.text s!"Good choice, I like {ans} too."}</p>
} />

#html <ProgWidget code={do
  initEdit { line := 449, character := 3 }
  let str ← askUserSelect 0 <p>What would you like to insert?</p> [
    ("Hello", <button>Hello</button>),
    ("World", <button>World</button>),
  ]
  insertLine ("-- "++str)
  let str ← askUserSelect 1 <p>What would you like to insert?</p> [
    ("Hello2", <button>Hello2</button>),
    ("World2", <button>World2</button>),
  ]
  askUserConfirm 1 <p>You are now inserting {.text str}</p>
  insertLine ("-- "++str)
  askUserConfirm 1 <p>Inserted</p>
} />


--









-- comment to keep document longer
