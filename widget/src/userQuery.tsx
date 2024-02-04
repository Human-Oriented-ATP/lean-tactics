import * as React from 'react';
import { TextDocumentEdit } from 'vscode-languageserver-protocol';
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

type Question = EmptyQ | FormQ | SelectQ | CustomQ | EditDocumentQ | ErrorQ
type Props = {code: MessageData, pos:DocumentPosition}

const dummyQuestion : EmptyQ = {kind:"empty"}

export default function InteractiveWidget(props: Props) {
  const [state, setState] = React.useState<[Question, any]>([dummyQuestion, null])
  const history = React.useRef<[Question,any][]>([])
  const [question, continuation] = state
  const rs = React.useContext(RpcContext)
  const ec = React.useContext(EditorContext)

  async function initForm() {
    const [nextQuestion, nextCont] = await rs.call<MessageData, [Question,any]>(
      'initializeInteraction', props.code)
    history.current = []
    setState([nextQuestion, nextCont])
  }
  async function sendAnswer(answer : any) {
    const [nextQuestion, nextCont] = await rs.call<any, [Question,any]>(
      'processUserAnswer', [answer, continuation])
      history.current.push(state)
      setState([nextQuestion, nextCont])
  }
  async function applyEdit(edit : TextDocumentEdit) {
    await ec.api.applyEdit({ documentChanges: [edit] })
    sendAnswer(null)
  }
  function undo() {
    const nextState = history.current.pop()
    if (nextState !== undefined) setState(nextState)
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
    case "editDocument":
      applyEdit(question.edit)
      break
    case "error":
      widget = <InteractiveMessageData msg={question.data} />
      break
  }
  return <div>
    <button onClick={undo}>Undo</button>
    {widget}
  </div>
}
