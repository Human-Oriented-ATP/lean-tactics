import MotivatedMoves.GUI.MotivatedProofPanel
import MotivatedMoves.GUI.DisplayTree
import MotivatedMoves.Moves

/-!

# Motivated proof list

This file implements the fron-facing UI for several motivated proof moves,
most of which are based on the tree representation
of the goal state developed in `ProofState/` and `Moves/`.

-/


open ProofWidgets Lean Meta Elab Tactic Server Widget

open Jsx OptionT

instance : Quote SubExpr.Pos `Tree.treePos where
  quote pos :=
  let posStx : TSyntaxArray `num := pos.toArray.map quote
  let args : Array Syntax := ⟨List.intersperse (.atom .none ",") posStx.toList⟩
  { raw := .node .none `Tree.treePos #[
    .atom .none "[",
    .node .none `null args,
    .atom .none "]"
  ] }

@[motivated_proof_move]
def tree_apply : InfoviewAction :=
  fun props => do
  let panelProps := props.toPanelWidgetProps
  if (panelProps.selectedLocations.size == 2) then
    let subexprPos := panelProps.selectedLocations
    let some pos1 := subexprPos[0]? | failure
    let some pos2 := subexprPos[1]? | failure
    let ⟨_, .target subexprPos1⟩ := pos1 | failure
    let ⟨_, .target subexprPos2⟩ := pos2 | failure
    let tac ← `(tactic| tree_apply $(quote subexprPos1) $(quote subexprPos2))
    let tac' ← `(tactic| tree_apply' $(quote subexprPos1) $(quote subexprPos2))
    let _ ← OptionT.mk <| withoutModifyingState <| try? <| evalTactic tac
    pure <DynamicEditButton
            label={"Apply"}
            range?={props.range}
            html?={<details «open»={true}>
        <summary className="mv2 pointer">{.text "Apply options"}</summary>
              <DynamicEditButton
                    label = "Discard the hypothesis"
                    range? = {props.range}
                    insertion? = {tac.raw.reprint.get!}
                    color = {"secondary"} />
                    <DynamicEditButton
                    label = "Preserve the hypothesis"
                    range? = {props.range}
                    insertion? = {tac'.raw.reprint.get!}
                    color = {"secondary"} />
                    </details>}
            vanish={true} />
  else failure

@[motivated_proof_move]
def tree_rewrite : InfoviewAction :=
  fun props => do
  let panelProps := props.toPanelWidgetProps
  if (panelProps.selectedLocations.size == 2) then
    let subexprPos := panelProps.selectedLocations
    let some pos1 := subexprPos[0]? | failure
    let some pos2 := subexprPos[1]? | failure
    let ⟨_, .target subexprPos1⟩ := pos1 | failure
    let ⟨_, .target subexprPos2⟩ := pos2 | failure
    let tac ← `(tactic| tree_rewrite $(quote subexprPos1) $(quote subexprPos2))
    let tac' ← `(tactic| tree_rewrite' $(quote subexprPos1) $(quote subexprPos2))
    let _ ← OptionT.mk <| withoutModifyingState <| try? <| evalTactic tac
    pure <DynamicEditButton
            label={"Rewrite"}
            range?={props.range}
            html?={<details «open»={true}>
        <summary className="mv2 pointer">{.text "Rewrite options"}</summary>
              <DynamicEditButton
                    label = "Discard the hypothesis"
                    range? = {props.range}
                    insertion? = {tac.raw.reprint.get!}
                    color = {"secondary"} />
                    <DynamicEditButton
                    label = "Preserve the hypothesis"
                    range? = {props.range}
                    insertion? = {tac'.raw.reprint.get!}
                    color = {"secondary"} />
                    </details>}
            vanish={true} />
  else failure

@[motivated_proof_move]
def tree_rewrite_ord : InfoviewAction :=
  fun props => do
    let panelProps := props.toPanelWidgetProps
    if (panelProps.selectedLocations.size == 2) then
      let subexprPos := panelProps.selectedLocations
      let some pos1 := subexprPos[0]? | failure
      let some pos2 := subexprPos[1]? | failure
      let ⟨_, .target subexprPos1⟩ := pos1 | failure
      let ⟨_, .target subexprPos2⟩ := pos2 | failure
      let tac ← `(tactic| tree_rewrite_ord $(quote subexprPos1) $(quote subexprPos2))
      let tac' ← `(tactic| tree_rewrite_ord' $(quote subexprPos1) $(quote subexprPos2))
      let _ ← OptionT.mk <| withoutModifyingState <| try? <| evalTactic tac
      pure <DynamicEditButton
            label={"Ordered rewrite"}
            range?={props.range}
            html?={<details «open»={true}>
        <summary className="mv2 pointer">{.text "Ordered rewrite options"}</summary>
              <DynamicEditButton
                    label = "Discard the hypothesis"
                    range? = {props.range}
                    insertion? = {tac.raw.reprint.get!}
                    color = {"secondary"} />
                    <DynamicEditButton
                    label = "Preserve the hypothesis"
                    range? = {props.range}
                    insertion? = {tac'.raw.reprint.get!}
                    color = {"secondary"} />
                    </details>}
            vanish={true} />
    else failure

@[motivated_proof_move]
def tree_simp : InfoviewAction :=
  fun props => do
    let panelProps := props.toPanelWidgetProps
    if (panelProps.selectedLocations.size == 1) then
      let some pos := panelProps.selectedLocations[0]? | failure
      let ⟨_, .target subexprPos⟩ := pos | failure
      let text := "tree_simp " ++ subexprPos.toArray.toList.toString
      pure
        <DynamicEditButton
          label={"Simplify"}
          range?={props.range}
          insertion?={text}
          html?={<p> Simplifying the target... </p>}
          vanish={true} />
    else failure

@[motivated_proof_move]
def tree_search : InfoviewAction := fun props => do
  if (props.selectedLocations.size == 0) then
      pure <DynamicEditButton
              label={"Search for redundant hypotheses and targets"}
              range?={props.range}
              insertion?={"tree_search"}
              html?={<p> Searching the tree... </p>}
              vanish={true} />
  else failure

@[motivated_proof_move]
def tree_induction : InfoviewAction :=
  fun props => do
    let panelProps := props.toPanelWidgetProps
    if (panelProps.selectedLocations.size == 1) then
      let some pos := panelProps.selectedLocations[0]? | failure
      let ⟨_, .target subexprPos⟩ := pos | failure
      let tac ← `(tactic| tree_induction $(quote subexprPos))
      let _ ← OptionT.mk <| withoutModifyingState <| try? <| evalTactic tac
      pure
        <DynamicEditButton
          label={"Perform Induction"}
          range?={props.range}
          insertion?={tac.raw.reprint.get!}
          html?={<p> Performing induction... </p>}
          vanish={true} />
    else failure

section LibraryPanelRendering

open Widget

def mkDiv (elems : Array Html) (cfg : Array (String × Json) := #[]) : Html :=
  .element "div" cfg elems

def Lean.Widget.CodeWithInfos.addDiffs (diffs : AssocList SubExpr.Pos DiffTag) (code : CodeWithInfos) : CodeWithInfos :=
  code.map fun info ↦
    match diffs.find? info.subexprPos with
      | some diff => { info with diffStatus? := some diff }
      |    none   =>   info

def Lean.Expr.renderWithDiffs (e : Expr) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do
  let e' := (← Widget.ppExprTagged e).addDiffs diffs
  return <InteractiveCode fmt={e'} />

def Lean.Name.renderWithDiffs (nm : Name) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do
  let env ← getEnv
  let some ci := env.find? nm | failure
  ci.type.renderWithDiffs diffs

def renderLibrarySearchResults (range : Lsp.Range) (label : String)
    (results : Array (Array (Name × (AssocList SubExpr.Pos DiffTag) × String) × Nat)) : MetaM Html := do
  let core ← mkDiv <$> results.mapM (renderBlock ·.fst)
  pure
    <details «open»={true}>
      <summary className="mv2 pointer">{.text label}</summary>
      {core}
    </details>
where
  renderBlock (results : Array _) : MetaM Html := do
    let block ← results.mapM fun (name, diffs, text) ↦ renderResult name diffs text
    return mkDiv (block.push <hr />)
  renderResult (name : Name) (diffs : AssocList SubExpr.Pos DiffTag) (text : String) : MetaM Html := do
    return mkDiv
      #[← name.renderWithDiffs diffs,
         <DynamicEditButton
            label={name.toString}
            range?={range}
            insertion?={text}
            variant={"text"}
            color={"info"}
            size={"small"} />]
      #[("display", "flex"), ("justifyContent", "space-between")]

end LibraryPanelRendering

open Jsx in
@[motivated_proof_move]
def libRewrite : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexpr := props.selectedLocations[0]? | failure
    let ⟨goal, .target pos⟩ := subexpr | failure
    let libSuggestions ← Tree.librarySearchRewrite (pos.toArray.toList) (← goal.getType)
    pure
      <DynamicEditButton
          label={"Rewrite with a theorem"}
          html?={← renderLibrarySearchResults props.range "Library search results" libSuggestions}
          vanish={true} />
  else failure

open Jsx in
@[motivated_proof_move]
def libRewriteOrd : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexpr := props.selectedLocations[0]? | failure
    let ⟨goal, .target pos⟩ := subexpr | failure
    let libSuggestions ← Tree.librarySearchRewriteOrd (pos.toArray.toList) (← goal.getType)
    pure
      <DynamicEditButton
          label={"Ordered rewrite with a theorem"}
          html?={← renderLibrarySearchResults props.range "Library search results" libSuggestions}
          vanish={true} />
  else failure

@[motivated_proof_move]
def libApply : InfoviewAction := fun props ↦ do
  let #[⟨goal, .target pos⟩] := props.selectedLocations | failure
  -- note that the library results are calculated twice. It should be made lazy in the future.
  let libSuggestions_delete ← Tree.librarySearchApply false pos.toArray.toList (← goal.getType)
  let libSuggestions_keep ← Tree.librarySearchApply true pos.toArray.toList (← goal.getType)
  let html_delete := ← renderLibrarySearchResults props.range "Library apply results" libSuggestions_delete
  let html_keep := ← renderLibrarySearchResults props.range "Library apply results" libSuggestions_keep
  pure
    <DynamicEditButton
        label={"Apply a theorem"}
        html?={<details «open»={true}>
        <summary className="mv2 pointer">{.text "Library apply options"}</summary>
              <DynamicEditButton
                    label = "Discard closed goal"
                    range? = {props.range}
                    html? = {html_delete}
                    color = {"secondary"} />
                    <DynamicEditButton
                    label = "Keep closed goal as hypothesis"
                    range? = {props.range}
                    html? = {html_keep}
                    color = {"secondary"} />
                    </details>} />

@[motivated_proof_move]
def push_neg : InfoviewAction := fun props ↦ do
  unless (props.selectedLocations.size == 1) do failure
  let some subexprPos := props.selectedLocations[0]? | failure
  let ⟨goal, .target pos⟩ := subexprPos | failure
  let (goalOuterPosition, goalPos) := Tree.splitPosition pos.toArray.toList
  unless (← Tree.withTreeSubexpr (← goal.getType) goalOuterPosition goalPos (fun _ x => pure x))
    matches Expr.app (.const ``Tree.Not _) _ do failure
  pure
    <DynamicEditButton
        label={"Push the negation"}
        range?={props.range}
        insertion?={"tree_push_neg " ++ ((SubExpr.Pos.toArray pos).toList).toString}
        vanish = {false} />

structure NamingButtonProps where
  selectedPos : String
deriving RpcEncodable

@[widget_module] def NamingButton : Component NamingButtonProps where
  javascript := include_str ".." / ".." / "build" / "js" / "namingButton.js"

-- TODO: add an option for naming the expression as a metavariable, using the `
@[motivated_proof_move]
def name : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨goal, .target pos⟩ := subexprPos | failure
    pure
      <DynamicEditButton
          label={"Give a name"}
          range?={props.range}
          html? = {<NamingButton selectedPos = {pos.toArray.toList.toString}/>}
          vanish = {true} />
  else failure

@[motivated_proof_move]
def unify : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨goal, .target pos⟩ := subexprPos | failure
    let (goalOuterPosition, goalPos) := Tree.splitPosition pos.toArray.toList
    unless (← Tree.withTreeSubexpr (← goal.getType) goalOuterPosition goalPos (fun _ x => pure x))
      matches Expr.app (.const ``Eq _) _ do failure
    pure
      <DynamicEditButton
          label={"Unify"}
          range?={props.range}
          insertion?={"lib_apply refl " ++ pos.toArray.toList.toString}
          vanish = {true} />
  else failure

@[motivated_proof_move]
def unfold_definition : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨_, .target pos⟩ := subexprPos | failure
    pure
      <DynamicEditButton
          label={"Unfold"}
          range?={props.range}
          insertion?={"tree_rewrite_def " ++ (pos.toArray.toList).toString}
          vanish = {true} />
  else failure

@[motivated_proof_move]
def unify_forall_exists : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨_, .target pos⟩ := subexprPos | failure
    let tac ← `(tactic| unify_forall_exists $(quote pos))
    let _ ← OptionT.mk <| withoutModifyingState <| try? <| evalTactic tac
    pure
      <DynamicEditButton
          label={"Unify existential with preceding forall"}
          range?={props.range}
          insertion?={tac.raw.reprint.get!}
          vanish = {true} />
  else failure

@[motivated_proof_move]
def contrapose_button : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 2) then
    let some subexprPos1 := props.selectedLocations[0]? | failure
    let ⟨_, .target pos1⟩ := subexprPos1 | failure
    let some subexprPos2 := props.selectedLocations[1]? | failure
    let ⟨_, .target pos2⟩ := subexprPos2 | failure
    let tac ← `(tactic| tree_contrapose $(quote pos1) $(quote pos2))
    let tac' ← `(tactic| tree_contrapose' $(quote pos1) $(quote pos2))
    let _ ← OptionT.mk <| withoutModifyingState <| try? <| evalTactic tac 
    pure
      <DynamicEditButton
          label={"Contrapose"}
          range?={props.range}
          html?={<details «open»={true}>
        <summary className="mv2 pointer">{.text "Contrapose options"}</summary>
              <DynamicEditButton
                    label = "Discard contraposed hypothesis"
                    range? = {props.range}
                    insertion?={tac.raw.reprint.get!}
                    color = {"secondary"} />
              <DynamicEditButton
                    label = "Keep contraposed hypothesis"
                    range? = {props.range}
                    insertion?={tac'.raw.reprint.get!}
                    color = {"secondary"} />
                    </details>}
          vanish = {true} />
  else failure


@[motivated_proof_move]
def swap_hyps : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨_, .target pos⟩ := subexprPos | failure
    let tac ← `(tactic| lib_rewrite Imp.swap $(quote pos))
    let _ ← OptionT.mk <| withoutModifyingState <| try? <| evalTactic tac 
    pure
      <DynamicEditButton
          label={"Swap the hypotheses"}
          range?={props.range}
          insertion?={tac.raw.reprint.get!}
          vanish = {true} />
  else failure
