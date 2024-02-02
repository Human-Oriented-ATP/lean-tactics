import * as React from 'react';
import { DocumentPosition, RpcContext, MessageData, InteractiveMessageData } from '@leanprover/infoview';
import HtmlDisplay, { Html } from './htmlDisplay';
// import { Html } from '@react-three/drei';

type EmptyQ = { kind:"empty", }
type FormQ = { kind:"form", elems:Html[] }
type SelectQ = { kind:"select", question:Html, options:Html[] }

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

type Question = EmptyQ | FormQ | SelectQ
type Props = {code: MessageData, pos:DocumentPosition}

const dummyQuestion : EmptyQ = {kind:"empty"}

export default function InteractiveWidget(props: Props) {
  const [question, setQuestion] = React.useState<Question>(dummyQuestion)
  const rs = React.useContext(RpcContext)

  async function initForm() {
    const nextQuestion = await rs.call<Props, Question>(
      'initializeInteraction', props)
    setQuestion(nextQuestion)
  }
  async function sendAnswer(answer : any){
    const nextQuestion = await rs.call<any, Question>(
      'processUserAnswer', answer)
    setQuestion(nextQuestion)
  }

  React.useEffect(() => {initForm()}, [props.code])
  switch (question.kind) {
    case "empty": return <EmptyWidget q={{}} answer={sendAnswer} pos={props.pos}/>
    case "form": return <FormWidget q={question} answer={sendAnswer} pos={props.pos}/>
    case "select": return <SelectWidget q={question} answer={sendAnswer} pos={props.pos}/>
  }
}
