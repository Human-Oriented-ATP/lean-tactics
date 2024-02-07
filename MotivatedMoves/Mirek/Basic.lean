import ProofWidgets.Component.Basic
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets
import ProofWidgets.Demos.InteractiveSvg

open Lean Server
open ProofWidgets

def hello := "world"
#eval hello

#eval let x : Nat := 4; x*x

/-

Theorem: ∑ i ∈ ι, f(i) < ω → |{i ∈ ι : f(i) > 0}| ≤ ℵ₀
Theorem: ∑ i ∈ ι, f(i) = 0 ↔ ∀ i ∈ ι, f(i) = 0

m : measure on α⁺
m(α⁺) > 0
m({x}) = 0
m is α⁺-additive

-- unfold α⁺-additive

m : measure on α⁺
m(α⁺) > 0
m({x}) = 0
∀ S* ⊆ 𝒫(α⁺), (|S*| ≤ α ∧ S* is pairwise disjoint)
  → m(⋃ S*) = ∑ a ∈ S*, m(a)

-- try S containing singletons

m : measure on α⁺
m(α⁺) > 0
m({x}) = 0
∀ S* ⊆ 𝒫(α⁺), (|S*| ≤ α ∧ S* is pairwise disjoint)
  → m(⋃ S*) = ∑ a ∈ S*, m(a)
this: ∀ X ⊆ α⁺, let S = {{x} : x ∈ X}, (|S| ≤ α ∧ S is pairwise disjoint)
  → m(⋃ S) = ∑ a ∈ S, m(a)

-- simplify this

m : measure on α⁺
m(α⁺) > 0
m({x}) = 0
∀ S* ⊆ 𝒫(α⁺), (|S*| ≤ α ∧ S* is pairwise disjoint)
  → m(⋃ S*) = ∑ a ∈ S*, m(a)
∀ X ⊆ α⁺, let S = {{x} : x ∈ X}, |X| ≤ α
  → m(X) = ∑ a ∈ X, m(0) = 0 (by Theorem)

-- how can we apply the same theorem in general in the original assumption?

if ∀ x ∈ S, m(x) = 0,
so we get a more general result:

m : measure on α⁺
m(α⁺) > 0
m({x}) = 0
∀ S ⊆ 𝒫(α⁺), (|S| ≤ α ∧ S is pairwise disjoint)
  → m(⋃ S) = ∑ a ∈ S, m(a)
∀ X ⊆ α⁺, let S = {{x} : x ∈ X}, |X| ≤ α
  → m(X) = ∑ a ∈ X, m(0) = 0 (by Theorem)
∀ S ⊆ 𝒫(α⁺), (|S| ≤ α ∧ S is pairwise disjoint ∧ ∀ x ∈ S, m(x) = 0)
  → m(⋃ S*) = 0

-- notice that this conclusion interacts with m(α⁺) > 0. So for each of these, we can conclude respectively X ≠ α⁺ and ⋂ S ≠ α⁺.



-- get rid of ∑, what to we know about ∑ ?


-/

/-
example : 1=1 := by
  refine (let x : ?A := ?B; ?C)
  case B =>
    refine ((fun (x : Nat) => ?B2 x) : (forall (x:Nat), ?A2))

  -- fun x => _ : forall x. ?P
  -/

example (x y z : Nat) : 1=1 := by
  let m := y+z
  rfl

open scoped ProofWidgets.Jsx
#html <SvgWidget html={init.html} state={init.state}/>

axiom interactive_goal_instance : Widget.InteractiveGoal
noncomputable instance : Inhabited Widget.InteractiveGoal where
  default := interactive_goal_instance

#check Svg
#check Svg.InteractiveSvg State
#check isvg
#check isvg.init
#check isvg.frame
#check isvg.render
#check (Svg isvg.frame)
#check (fun (x : Svg isvg.frame) => Svg.idToDataList x)
-- #check isvg.render 0 none none isvg.init

#synth RpcEncodable PanelWidgetProps

open Lean ProofWidgets Server

structure TestWidgetProps where
  count : Nat
deriving ToJson, FromJson

@[widget_module]
def TestWidget : Component TestWidgetProps where
  javascript := "
    import { RpcContext, mapRpcError } from '@leanprover/infoview'
    import * as React from 'react';

    export default function(props) {
      const maxCount = React.useRef(0);
      const [tickCount,setTickCount] = React.useState(0);
      const [tickCount2,setTickCount2] = React.useState(0);
      function init_fun() {
        console.log('Init'+props.count)
      }
      // React.useEffect(init_fun);
      React.useMemo(init_fun, []);
      console.log(`Call ${props.count}, ${tickCount}, ${tickCount2}`)
      if(true) setTimeout(
        () => {
          console.log('Tick'+props.count)
          var nextTickCount = 42
          if(tickCount == 10) nextTickCount = 10
          else nextTickCount = tickCount+1
          console.log(`Next: ${nextTickCount}`)
          setTickCount(nextTickCount);
          setTickCount2(nextTickCount);
        },
        1000
      )

      if (props.count > maxCount.current) {
        maxCount.current = props.count;
      }
      return React.createElement('div', {},
        React.createElement('p', {}, 'The number of hypotheses is ', props.count),
        React.createElement('p', {}, 'The max count is ', maxCount.current),
        React.createElement('p', {}, 'tickCount: ', tickCount),
        React.createElement('p', {}, 'tickCount2: ', tickCount2)
      );
    }
  "

#html <TestWidget count={0}/>

def newState : State := {
  points := init.state.state.points,
  color := (0.7, 0.7, 0.7)
}

@[server_rpc_method]
def FancyWidget.rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let numHyps :=
      if let .some goal := props.goals[0]? then
        goal.hyps.size
      else 0
    -- let mut points : Array (Float × Float) := #[]
    -- for i in [1:numHyps] do
    --   points := points.push (0.0, 0.0)
    let newState : State := {
      points := init.state.state.points,
      color := match numHyps with
      | 0 => (0.7, 0.7, 0.7)
      | 1 => (0.0, 0.7, 0.7)
      | 2 => (0.7, 0.0, 0.7)
      | _ => (0.7, 0.7, 0.0)
    }
    return <div>
      <p>Number of hypotheses: {.text $ toString numHyps}</p>
      <TestWidget count = {numHyps}/>
      <SvgWidget html={init.html} state={{init.state with state := newState}}/>
    </div>

@[widget_module]
def FancyWidget : Component PanelWidgetProps :=
  mk_rpc_widget% FancyWidget.rpc

example : 1=1 ∧ 2=2 := by
  with_panel_widgets [FancyWidget]
  let x := 5
  let y := 6
  constructor
