import * as React from 'react';
import { TextEdit, TextDocumentEdit } from 'vscode-languageserver-protocol';
import { EditorContext, DocumentPosition, RpcContext, MessageData, InteractiveMessageData } from '@leanprover/infoview';
import HtmlDisplay, { Html } from './htmlDisplay';
import { ReactJSXElement } from '@emotion/react/types/jsx-namespace';

// import { Html } from '@react-three/drei';

interface ProgWidgetContext {
  answer (arg : any) : void
  pos : DocumentPosition
}

const progWidgetContext = React.createContext<ProgWidgetContext>({
  answer : (ans) => { console.warn(`Uncaptured answer: ${ans}`) },
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
    <div ref={optionsRef}>
    {props.options.map((option,i) => {
      return <HtmlDisplayClickable
        html={option}
        pos={ctx.pos}
        onClick={() => ctx.answer(i)} />
    })}
    </div>
  </div>
}

type Props = {code: MessageData, pos:DocumentPosition}

type WidgetQuery =
  { widget : { w : Html } } |
  { editDocument : { edit : TextDocumentEdit } }

const dummyQuestion = { text: "" } 

interface History {
  state : [Html,any]
  edits : TextDocumentEdit[]
}

export default function InteractiveWidget(props: Props) {
  const [state, setStateRaw] = React.useState<[Html, any]>([dummyQuestion, null])
  const history = React.useRef<History[]>([])
  const [question, continuation] = state
  const rs = React.useContext(RpcContext)
  const ec = React.useContext(EditorContext)

  async function setState(nextState : [WidgetQuery, any]) {
    while (true) {
      const [question, cont] = nextState
      console.log("Question structure")
      console.log(question)
      if ("editDocument" in question) {
        const edit : TextDocumentEdit = question.editDocument.edit
        if (history.current.length > 0) {
          const last = history.current[history.current.length-1]
          last.edits.push(edit)
        }
        await ec.api.applyEdit({ documentChanges: [edit] })

        nextState = await rs.call<any, [WidgetQuery,any]>(
          'processUserAnswer', [null, cont])
      }
      else {
        setStateRaw([question.widget.w, cont])
        break
      }
    }
  }

  async function initForm() {
    const nextState = await rs.call<MessageData, [WidgetQuery,any]>(
      'initializeInteraction', props.code)
    history.current = []
    setState(nextState)
  }
  async function sendAnswer(answer : any) {
    const nextState = await rs.call<any, [WidgetQuery,any]>(
      'processUserAnswer', [answer, continuation])
      history.current.push({ state: state, edits:[] })
      setState(nextState)
  }

  function reverseBasicEdit(e : TextEdit) : TextEdit {
    // calculate pasted range
    const lines = e.newText.split("\n")
    const endLine = e.range.start.line + (lines.length-1)
    var endCharacter = lines[lines.length-1].length
    if (lines.length == 1) endCharacter += e.range.start.character
    
    // we cannot recover the original text, so we fill it with spaces
    var dummyText = ""
    if (e.range.start.line == e.range.end.line)
      dummyText = " ".repeat(e.range.end.character - e.range.start.character)
    else
      dummyText = "\n".repeat(e.range.end.line - e.range.start.line) + " ".repeat(e.range.end.character)

    const res = {
      range: {
        start: e.range.start,
        end:{ line: endLine, character: endCharacter }
      },
      newText: dummyText
    }
    console.log(res)
    return res
  }
  async function unapplyEdits(edits : TextDocumentEdit[]) {
    for (var i=edits.length-1; i >= 0; i--) {
      const edit = edits[i]
      const revedit : TextDocumentEdit = {
        textDocument: edit.textDocument,
        edits: edit.edits.map(reverseBasicEdit)
      }
      await ec.api.applyEdit({ documentChanges: [revedit] })
    }
  }
  function undo() {
    console.log(history)
    const last = history.current.pop()
    if (last !== undefined) {
      setStateRaw(last.state)
      unapplyEdits(last.edits)
    }
  }

  React.useEffect(() => {initForm()}, [props.pos.line])
  var widget : ReactJSXElement = <div/>
  
  return <div>
    <button onClick={undo}>Undo</button>
    <hr/>
    <progWidgetContext.Provider value={{
      answer : sendAnswer,
      pos : props.pos
    }}>
      <HtmlDisplay pos={props.pos} html={question} />
    </progWidgetContext.Provider>
  </div>
}
