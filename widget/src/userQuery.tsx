import * as React from 'react';
import { TextEdit, TextDocumentEdit } from 'vscode-languageserver-protocol';
import { EditorContext, DocumentPosition, RpcContext, MessageData, InteractiveMessageData } from '@leanprover/infoview';
import HtmlDisplay, { Html } from './htmlDisplay';
import { ReactJSXElement } from '@emotion/react/types/jsx-namespace';

// import { Html } from '@react-three/drei';

type EmptyQ = { kind:"empty", }
type FormQ = { kind:"form", elems:Html[] }
type SelectQ = { kind:"select", question:Html, options:Html[] }
type CustomQ = { kind: "custom", code:Html }
type EditDocumentQ = { kind: "editDocument", edit:TextDocumentEdit }
type ErrorQ = { kind:"error", data:MessageData }

interface WidgetProps<Q> {
  q : Q
  answer (a : any) : void
  pos : DocumentPosition
}

function EmptyWidget (props : WidgetProps<{}>) {
  return <div>
    <p>No questions...</p>
  </div>
}

function FormWidget (props : WidgetProps<FormQ>) {
  function answer(event:React.FormEvent<HTMLFormElement>) {
    event.preventDefault()
    const data = new FormData(event.currentTarget)
    props.answer(Object.fromEntries(data))
  }
  const formRef = React.useRef<HTMLFormElement>(null)

  React.useEffect(() => {
    if(formRef.current !== null)
      formRef.current.reset()
  }, [props.q.elems])

  return <form onSubmit={answer} ref={formRef}>
    {props.q.elems.map(html =>
    <HtmlDisplay pos={props.pos} html={html} />)}
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

function SelectWidget (props : WidgetProps<SelectQ>) {

  const optionsRef = React.useRef<HTMLDivElement>(null)

  return <div>
    <HtmlDisplay pos={props.pos} html={props.q.question} />
    <div ref={optionsRef}>
    {props.q.options.map((option,i) => {
      return <HtmlDisplayClickable
        html={option}
        pos={props.pos}
        onClick={() => props.answer(i)} />
    })}
    </div>
  </div>
}

function CustomWidget (props : WidgetProps<CustomQ>) {
  return <HtmlDisplay pos={props.pos} html={props.q.code} />;
}

type Question = EmptyQ | FormQ | SelectQ | CustomQ | ErrorQ
type QuestionE = Question | EditDocumentQ
type Props = {code: MessageData, pos:DocumentPosition}

const dummyQuestion : EmptyQ = {kind:"empty"}

interface History {
  state : [Question,any]
  edits : TextDocumentEdit[]
}

export default function InteractiveWidget(props: Props) {
  const [state, setStateRaw] = React.useState<[Question, any]>([dummyQuestion, null])
  const history = React.useRef<History[]>([])
  const [question, continuation] = state
  const rs = React.useContext(RpcContext)
  const ec = React.useContext(EditorContext)

  async function setState(nextState : [QuestionE, any]) {
    while (true) {
      const [question, cont] = nextState
      if (question.kind == "editDocument") {
        const edit : TextDocumentEdit = question.edit
        if (history.current.length > 0) {
          const last = history.current[history.current.length-1]
          last.edits.push(edit)
        }
        await ec.api.applyEdit({ documentChanges: [edit] })

        nextState = await rs.call<any, [QuestionE,any]>(
          'processUserAnswer', [null, cont])
      }
      else {
        setStateRaw([question, cont])
        break
      }
    }
  }

  async function initForm() {
    const nextState = await rs.call<MessageData, [QuestionE,any]>(
      'initializeInteraction', props.code)
    history.current = []
    setState(nextState)
  }
  async function sendAnswer(answer : any) {
    const nextState = await rs.call<any, [QuestionE,any]>(
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
      setState(last.state)
      unapplyEdits(last.edits)
    }
  }

  React.useEffect(() => {initForm()}, [props.pos.line])
  var widget : ReactJSXElement = <div/>
  switch (question.kind) {
    case "empty":
      widget = <EmptyWidget q={{}} answer={sendAnswer} pos={props.pos}/>
      break
    case "form":
      widget = <FormWidget q={question} answer={sendAnswer} pos={props.pos}/>
      break
    case "select":
      widget = <SelectWidget q={question} answer={sendAnswer} pos={props.pos}/>
      break
    case "custom":
      widget = <CustomWidget q={question} answer={sendAnswer} pos={props.pos} />
      break
    case "error":
      widget = <InteractiveMessageData msg={question.data} />
      break
  }
  return <div>
    <button onClick={undo}>Undo</button>
    <hr/>
    {widget}
  </div>
}
