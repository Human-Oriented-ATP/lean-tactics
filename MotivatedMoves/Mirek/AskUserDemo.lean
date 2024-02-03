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
