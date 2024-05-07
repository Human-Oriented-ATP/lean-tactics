import * as React from 'react';
import { TextEdit, TextDocumentEdit, OptionalVersionedTextDocumentIdentifier, Position } from 'vscode-languageserver-protocol';
import { EditorContext, DocumentPosition, RpcContext, MessageData, InteractiveMessageData } from '@leanprover/infoview';
import HtmlDisplay, { Html } from './htmlDisplay';
import { ReactJSXElement } from '@emotion/react/types/jsx-namespace';

// import { Html } from '@react-three/drei';

interface ProgWidgetContext {
  answer (arg : any) : void
  pos : DocumentPosition
}
function dummyAnswer(ans : any) {
  console.warn(`Uncaptured answer: ${ans}`)
}

const progWidgetContext = React.createContext<ProgWidgetContext>({
  answer : dummyAnswer,
  pos : { uri: "dummy", line:0, character:0 }
})

export function EmptyWidget (props : {}) {
  return <div>
    <p>No questions...</p>
  </div>
}

export function FormWidget (props : { elems : Html[] }) {
  const ctx = React.useContext(progWidgetContext)
  function answer(event:React.FormEvent<HTMLFormElement>) {
    event.preventDefault()
    const data = new FormData(event.currentTarget)
    ctx.answer(Object.fromEntries(data))
  }
  const formRef = React.useRef<HTMLFormElement>(null)

  React.useEffect(() => {
    if(formRef.current !== null)
      formRef.current.reset()
  }, [props.elems])

  return <form onSubmit={answer} ref={formRef}>
    {props.elems.map(html =>
    <HtmlDisplay pos={ctx.pos} html={html} />)}
  </form>
}

interface HtmlDisplayClickableProps {
  html : Html
  pos : DocumentPosition
  onClick () : void
}

function htmlAddOnClick (html : Html, onClick : {() : void})
: Html
{
  if (!("element" in html)) return html
  const [name, attrs, children] = html.element
  if (name == "button" || name == "a") {
    const attrs2 = attrs.slice()
    if (name == "a") attrs2.push(["className", "pointer dim"])
    attrs2.push(["onClick", onClick])
    return { element: [name, attrs2, children] }
  }
  else {
    return {
      element: [name, attrs, children.map(child => {
        return htmlAddOnClick(child, onClick)
      })]
    }
  }
}

function HtmlDisplayClickable (props : HtmlDisplayClickableProps) {
  return <HtmlDisplay html={htmlAddOnClick(props.html, props.onClick)} pos={props.pos}/>
}

export function SelectWidget (props : { question : Html, options : Html[] }) {

  const optionsRef = React.useRef<HTMLDivElement>(null)
  const ctx = React.useContext(progWidgetContext)

  return <div>
    <HtmlDisplay pos={ctx.pos} html={props.question} />
    <div style={{display: "grid", alignItems: "center", justifyItems: "center"}} ref={optionsRef}>
    {props.options.map((option,i) => {
      return <div className="grid-item">
        <HtmlDisplayClickable
          html={option}
          pos={ctx.pos}
          onClick={() => ctx.answer(i)} />
        </div>
    })}
    </div>
    </div>
}

interface EditProps {
  ident: OptionalVersionedTextDocumentIdentifier,
  startPos: Position,
}
interface Props {
  code: MessageData,
  pos: DocumentPosition,
}

type WidgetQuery =
  { widget : { level: number, w : Html } } |
  { insertLine : { line : string } } |
  { initEdit : EditProps }

const dummyQuestion = { text: "" } 

interface ProgWidgetState {
  level : number,
  widget : JSX.Element,
  editPos: Position,
  parent? : ProgWidgetState
  previous? : ProgWidgetState
}
const iniState : ProgWidgetState = {
  level : 0,
  editPos : {line : 0, character : 0},
  widget : <p>Initializing...</p>,
}

export default function ProgWidget(props: Props) {
  const [state, setState] = React.useState<ProgWidgetState>(iniState)
  const rs = React.useContext(RpcContext)
  const ec = React.useContext(EditorContext)
  const editCursor = React.useRef<Position>({line:0, character:0})
  const editProps = React.useRef<EditProps | null>(null)

  // Document editing

  async function editDocumentAsync(edit : TextDocumentEdit, pos: DocumentPosition) {
    await ec.api.applyEdit({ documentChanges: [edit] })
    await ec.revealPosition(pos)
  }
  function editDocument(pos : Position, newLines : string[]) {
    if (editProps.current === null) {
      if (newLines.length > 0) {
        console.warn("Document editing not initialized, cannot insert:")
        console.warn(newLines)
      }
      return
    }
    if (pos === editCursor.current && newLines.length === 0) return

    var newText : string = newLines.map(x => x+'\n').join('').trimEnd()
    if (newLines.length === 0) editCursor.current = pos 
    else editCursor.current = { line: pos.line + newLines.length, character : newLines[newLines.length-1].length }
    if (pos.character !== 0) {
      newText = '\n'+newText
      editCursor.current = {
        line : editCursor.current.line + 1,
        character : newLines[newLines.length-1].length,
      }
    }
    const range = { start : pos, end : editCursor.current }
    editDocumentAsync({
      textDocument: editProps.current.ident,
      edits: [{ range: range, newText: newText }]
    }, {
      ...editCursor.current,
      uri: editProps.current.ident.uri
    })
  }

  // Widget composition

  function buildNextState(
      prevState : ProgWidgetState | undefined,
      level : number,
      html : Html,
      cont : MessageData
    ) : ProgWidgetState {

    const editPos = editCursor.current

    // Process next answer

    async function sendAnswer(answer : any) {
      console.log("Answer:")
      console.log(answer)
      var cont2 = cont
      const newLines : string[] = []
      while (true) {
        const queryCont = await rs.call<[any,MessageData], [WidgetQuery,MessageData]>(
          'processUserAnswer', [answer, cont2])
        const query = queryCont[0]
        cont2 = queryCont[1]
        answer = null
        if ("insertLine" in query) {
          newLines.push(query.insertLine.line)
        }
        else if ("initEdit" in query) {
          console.warn("initEdit is only available suring initialization")
        }
        else {
          editDocument(editPos, newLines)
          setState(buildNextState(
            nextState,
            query.widget.level,
            query.widget.w,
            cont2,
          ))  
          break
        }
      }
    }

    // Build widget

    const widget = <progWidgetContext.Provider value={{
        answer : sendAnswer,
        pos : props.pos
      }}>
        <HtmlDisplay html={html} pos={props.pos}/>
      </progWidgetContext.Provider>

    // Insert to the state

    var parent : ProgWidgetState | undefined = prevState
    while (parent !== undefined && parent.level >= level)
      parent = parent.parent
    const nextState = {
      level : level,
      widget : widget,
      editPos : editPos,
      parent : parent,
      previous : prevState,
    }
    return nextState
  }
  async function initialize() {
    var [query,cont] = await rs.call<MessageData, [WidgetQuery,MessageData]>(
      'initializeInteraction', props.code)
    editProps.current = null
    while (true) {
      if ("insertLine" in query) {
        console.warn("Edits disabled before user action")
      }
      else if ("initEdit" in query) {
        editProps.current = query.initEdit
      }
      else {
        if (editProps.current)
          editCursor.current = editProps.current.startPos
        setState(buildNextState(
          undefined,
          query.widget.level,
          query.widget.w,
          cont,
        ))
        break
      }
      [query,cont] = await rs.call<[null,MessageData], [WidgetQuery,MessageData]>(
        'processUserAnswer', [null, cont])
    }
  }
  function undo() {
    console.log("Undo")
    console.log(state)
    if (state.previous === undefined) return
    editDocument(state.previous.editPos, [])
    setState(state.previous)
  }

  React.useEffect(() => { initialize() }, [props.pos.line])

  // Rendering

  const widgets : JSX.Element[] = []
  var x : ProgWidgetState | undefined = state
  while (x !== undefined) {
    widgets.push(x.widget)
    x = x.parent
  }
  widgets.reverse()
  return <div>
    <button onClick={undo}>Undo</button>
    <hr/>
    {widgets}
  </div>
}
