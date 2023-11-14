import ProofWidgets

open Lean Server ProofWidgets Jsx

structure NoProps where
deriving RpcEncodable

@[server_rpc_method]
def TestWidget.rpc (_props : NoProps) : RequestM (RequestTask Html) := do
  RequestM.asTask do
    return .ofComponent PenroseDiagram {
      embeds := #[("A", .ofComponent PenroseDiagram {
        embeds := #[("A", <p> Hello </p>)],
        dsl := "type Set",
        sty := "
forall Set x {
    x.icon = Circle {
        strokeWidth : 0.0
    }
    x.textBox = Rectangle {
        fontSize : \"25px\"
    }
}
",
        sub := "
Set A
Set B
"
        } #[])],
      dsl := "type Set",
      sty := "
forall Set x {
    x.icon = Circle {
        strokeWidth : 0.0
    }
    x.textBox = Rectangle {
        fontSize : \"25px\"
    }
}
",
      sub := "
Set A
Set B
"
    } #[]

@[widget_module]
def TestWidget : Component NoProps :=
  mk_rpc_widget% TestWidget.rpc

#html <TestWidget />