import MotivatedMoves.Mirek.AskUser
import ProofWidgets

open Lean ProofWidgets Server
open ProofWidgets.Jsx

structure InteractiveWidgetProps where
  code : InteractiveM Unit
deriving Server.RpcEncodable

@[widget_module]
def ProgramableWidget : Component InteractiveWidgetProps where
  javascript := include_str ".." / ".." / "build" / "js" / "userQuery.js"

#check Elab.Term.TermElabM

def showIGoal : TacticIM Unit := do
  let goal : Format ← Lean.Elab.Tactic.withMainContext do
    let goal ← Elab.Tactic.getMainGoal
    Elab.Term.ppGoal goal
  askUserConfirm <p>{.text s!"The goal is {goal}"}</p>

def showGoal : Elab.Tactic.TacticM Unit := do
  let goal : Format ← Lean.Elab.Tactic.withMainContext do
    let goal ← Elab.Tactic.getMainGoal
    Elab.Term.ppGoal goal
  logInfo m!"The goal is {goal}"

syntax (name:=InteractiveTac) "interactive_tac" tacticSeq : tactic

@[tactic InteractiveTac]
def InteractiveTacImpl:Lean.Elab.Tactic.Tactic
| stx@`(tactic|interactive_tac $seq) => do
  let tacs ← (match seq with
    | `(Lean.Parser.Tactic.tacticSeq| $[$tacs]*)
    | `(Lean.Parser.Tactic.tacticSeq| { $[$tacs]* }) =>
      return tacs
    | _ => Lean.Elab.throwUnsupportedSyntax
  )
  let some ⟨stxStart, _⟩ := (←getFileMap).rangeOfStx? stx | return
  let current_code : TacticIM Unit := (do
    showIGoal
    for tac in tacs do
      askUserConfirm (.text <| toString tac)
      let goalFmt ← ((do
        Lean.Elab.Tactic.evalTactic tac
        Lean.Elab.Tactic.withMainContext do
          let goal ← Elab.Tactic.getMainGoal
          Elab.Term.ppGoal goal
      ) : Elab.Tactic.TacticM Format)
      askUserConfirm <p>{.text <| toString goalFmt}</p>
      showIGoal
  )
  let raw_code ← current_code.run
  let current_code2 : Elab.Tactic.TacticM Unit := (do
    showGoal
    for tac in tacs do
      logInfo tac
      Lean.Elab.Tactic.evalTactic tac
      showGoal
  )
  current_code2

  Widget.savePanelWidgetInfo (hash ProgramableWidget.javascript) (do
    let jsonCode ← rpcEncode raw_code
    return json%{
      code : $jsonCode
    }
  ) stx
| _ => Lean.Elab.throwUnsupportedSyntax

example (a b c d : Prop) (h1 : a → b) (h2 : b → c) (h3 : c → d) : d := by
  interactive_tac
    apply h3
    apply h2
    apply h1

example (a b c d : Nat) (h : c+b*a = d) : a*b+c = d := by
  interactive_tac
    rewrite [Nat.mul_comm]
    rewrite [Nat.add_comm]

#html <ProgramableWidget code={do
  let name ← askUserString <p>What is your name?</p>
  let surname ← askUserString <p>Hi {.text name}, what is your surname?</p>
  askUserConfirm <p>{.text s!"Nice to meet you, {name} {surname}"}</p>
} />
#html <ProgramableWidget code={do
  let teletubie : String ← askUserSelect <p>Favorite color?</p> [
    ("Tinky Winky", <button style={Json.mkObj [("background-color", "purple"), ("color", "white")]}>purple</button>),
    ("Dipsy", <button style={Json.mkObj [("background-color", "green"), ("color", "white")]}>green</button>),
    ("Laa-Laa", <button style={Json.mkObj [("background-color", "yellow")]}>yellow</button>),
    ("Po", <button style={Json.mkObj [("background-color", "red"), ("color", "white")]}>red</button>)
  ]
  let response ← askUserString <p>{.text s!"OMG, how can you like the color of {teletubie}, the most annoying of all Teletubbies??"}</p>
  let i ← askUserInt <p>{.text s!"What do you mean by '{response}'? Let's try something different. I am thinking of a number, try to guess it."}</p>
  let i ← askUserInt <p>{.text s!"Oh, you thought {i}? That was close, I was thinking of {i+1}. Let's try again."}</p>
  throw $ .inl $ Exception.internal ⟨4⟩
  throwWidgetError "Sorry, I played with exceptions"
  let _ ← askUserInt <p>{.text s!"Oh, you thought {i}? That was close, I was thinking of {i+1}. Let's try again."}</p>
} />
#html <ProgramableWidget code={do
  let ans ← askUserSelect <div/> [
    ("You clicked a link", <div>Click <a>here</a></div>),
    ("You clicked a button", <div> or <button>here</button></div>),
  ]
  askUserConfirm <| Html.text <| toString ans
  let ans ← askUserForm <form>
    <p><label>Username: </label>
    <input name="str" type="string"/></p>
    <p><label>Password: </label>
    <input name="pass" type="password"/></p>
    <p><label>Age: </label>
    <input name="num" type="number"/></p>
    <input type="submit"/>
  </form>
  askUserConfirm <| Html.text <| toString ans
  let ans ← askUserInput <p>Now a <b>real </b> favorite color</p> <input type="color" defaultValue="#00ffff"/>
  askUserConfirm <| <p>{.text s!"Good choice, I like {ans} too."}</p>
} />

#html <ProgramableWidget code={do
  let str ← askUserSelect <p>What would you like to insert?</p> [
    ("Hello", <button>Hello</button>),
    ("World", <button>World</button>),
  ]
  insertLine 90 ("-- "++str)
}/>
