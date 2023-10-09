import LeanTactics.MotivatedProofPanel
import TreeMoves.TreeRewrite
import TreeMoves.TreeMoves
import Skolem

/-!

# Motivated proof list

This file implements several motivated proof moves,
most of which are based on the tree representation
of the goal state developed in `TreeMoves`.

-/


open ProofWidgets Lean Meta Server Widget

open Jsx OptionT

@[motivated_proof_move]
def tree_apply : InfoviewAction := 
  fun props => do
  let panelProps := props.toPanelWidgetProps
  if (panelProps.selectedLocations.size == 2) then
    let subexprPos := panelProps.selectedLocations
    let some pos1 := subexprPos[0]? | failure
    let some pos2 := subexprPos[1]? | failure
    let ⟨_, .target subexprPos1⟩  := pos1 | failure
    let ⟨_, .target subexprPos2⟩ := pos2 | failure
    let text := subexprPos1.toArray.toList.toString ++ " " ++ 
                  subexprPos2.toArray.toList.toString
    pure <DynamicEditButton 
            label={"Apply"} 
            range?={props.range} 
            html?={<details «open»={true}>
        <summary className="mv2 pointer">{.text "Apply options"}</summary>
              <DynamicEditButton
                    label = "Delete the hypothesis"
                    range? = {props.range}
                    insertion? = {"tree_apply " ++ text}
                    color = {"secondary"} />
                    <DynamicEditButton
                    label = "Preserve the hypothesis"
                    range? = {props.range}
                    insertion? = {"tree_apply' " ++ text}
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
    let text := (subexprPos1.toArray.toList.toString ++ " " ++ 
              subexprPos2.toArray.toList.toString)
    pure <DynamicEditButton 
            label={"Rewrite"} 
            range?={props.range} 
            html?={<details «open»={true}>
        <summary className="mv2 pointer">{.text "Rewrite options"}</summary>
              <DynamicEditButton
                    label = "Delete the hypothesis"
                    range? = {props.range}
                    insertion? = {"tree_rewrite " ++ text}
                    color = {"secondary"} />
                    <DynamicEditButton
                    label = "Preserve the hypothesis"
                    range? = {props.range}
                    insertion? = {"tree_rewrite' " ++ text}
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
      let text := (subexprPos1.toArray.toList.toString ++ " " ++ 
              subexprPos2.toArray.toList.toString)
      pure <DynamicEditButton 
            label={"Ordered rewrite"} 
            range?={props.range} 
            html?={<details «open»={true}>
        <summary className="mv2 pointer">{.text "Ordered rewrite options"}</summary>
              <DynamicEditButton
                    label = "Delete the hypothesis"
                    range? = {props.range}
                    insertion? = {"tree_rewrite_ord " ++ text}
                    color = {"secondary"} />
                    <DynamicEditButton
                    label = "Preserve the hypothesis"
                    range? = {props.range}
                    insertion? = {"tree_rewrite_ord' " ++ text}
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
          label={"Simplify the expression"} 
          range?={props.range} 
          insertion?={text} 
          html?={<p> Simplifying the target... </p>}
          vanish={true} />
    else failure

@[motivated_proof_move]
def tree_search : InfoviewAction := fun props => do
  if (props.selectedLocations.size == 0) then
      pure <DynamicEditButton 
              label={"Search for redundancy"} 
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
      let text := "tree_induction " ++ subexprPos.toArray.toList.toString
      pure 
        <DynamicEditButton 
          label={"Perform Induction"} 
          range?={props.range} 
          insertion?={text} 
          html?={<p> Performing induction... </p>}
          vanish={true} />
    else failure

-- TODO: Move

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

open Jsx in
@[motivated_proof_move]
def libRewrite : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexpr := props.selectedLocations[0]? | failure
    let ⟨goal, .target pos⟩ := subexpr | failure
    let libSuggestions ← Tree.librarySearchRewrite (pos.toArray.toList) (← goal.getType)
    pure
      <DynamicEditButton 
          label={"Rewrite with a library result"}
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
          label={"Ordered rewrite with a library result"}
          html?={← renderLibrarySearchResults props.range "Library search results" libSuggestions}
          vanish={true} />
  else failure

@[motivated_proof_move]
def libApply : InfoviewAction := fun props ↦ do
  let #[⟨goal, .target pos⟩] := props.selectedLocations | failure
  let libSuggestions_delete ← Tree.librarySearchApply false pos.toArray.toList (← goal.getType)
  let libSuggestions_keep ← Tree.librarySearchApply true pos.toArray.toList (← goal.getType)
  let html_delete := ← renderLibrarySearchResults props.range "Library apply results" libSuggestions_delete
  let html_keep := ← renderLibrarySearchResults props.range "Library apply results" libSuggestions_keep
  pure
    <DynamicEditButton 
        label={"Apply a library result"} 
        html?={<details «open»={true}>
        <summary className="mv2 pointer">{.text "Ordered rewrite options"}</summary>
              <DynamicEditButton
                    label = "Delete closed subgoals"
                    range? = {props.range}
                    html? = {html_delete}
                    color = {"secondary"} />
                    <DynamicEditButton
                    label = "Preserve closed subgoals as hypotheses"
                    range? = {props.range}
                    html? = {html_keep}
                    color = {"secondary"} />
                    </details>} />

@[motivated_proof_move]
def libApplyKeepingTarget : InfoviewAction := fun props ↦ do
  let #[⟨goal, .target pos⟩] := props.selectedLocations | failure
  let libSuggestions ← Tree.librarySearchApply true pos.toArray.toList (← goal.getType)
  pure
    <DynamicEditButton 
        label={"Apply a library result keeping the conclusion in the context"} 
        html?={← renderLibrarySearchResults props.range "Library apply results" libSuggestions} />

--TODO check if selected expression starts with `¬`
@[motivated_proof_move]
def push_neg : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨goal, .target pos⟩ := subexprPos | failure
    let (goalTreePos, goalPos) := Tree.splitPosition pos.toArray.toList
    -- not sure the next two lines are doing exactly what I want them to
    let expr : Expr ← Tree.withTreeSubexpr (← goal.getType) goalTreePos goalPos (fun _ x => pure x)
    let (.app (.const `Not _) _) := expr | failure
    pure
      <DynamicEditButton 
          label={"Push the negation through"}
          range?={props.range} 
          insertion?={"tree_push_neg " ++ ((SubExpr.Pos.toArray pos).toList).toString}
          vanish = {false} />
  else failure

structure NamingButtonProps where 
  selectedPos : String
deriving RpcEncodable

@[widget_module] def NamingButton : Component NamingButtonProps where
  javascript := include_str ".." / "build" / "js" / "namingButton.js"


@[motivated_proof_move]
def name : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨_, .target pos⟩ := subexprPos | failure
    pure
      <DynamicEditButton 
          label={"Name the expression"}
          range?={props.range} 
          html? = {<NamingButton selectedPos = {pos.toArray.toList.toString}/>}
          vanish = {true} />
  else failure

@[motivated_proof_move]
def unify : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨_, .target pos⟩ := subexprPos | failure
    pure
      <DynamicEditButton 
          label={"Unify the relation"}
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
          label={"Unfold definition"}
          range?={props.range} 
          insertion?={"tree_rewrite_def " ++ (pos.toArray.toList).toString}
          vanish = {true} />
  else failure

@[motivated_proof_move]
def unify_forall_exists : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨_, .target pos⟩ := subexprPos | failure
    pure
      <DynamicEditButton 
          label={"Unify an existential with a preceding forall"}
          range?={props.range} 
          insertion?={"unify_forall_exists " ++ (pos.toArray.toList).toString}
          vanish = {true} />
  else failure

/- temporary lemma for the `contraposition` step -/
lemma contrapose : (¬p → ¬q) ↔ (q → p) := ⟨fun h hq => Classical.byContradiction fun hp => h hp hq, mt⟩

/-- would be nice to have the contraposition step working for two selected expressions -/
@[motivated_proof_move]
def contrapose_button : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨_, .target pos⟩ := subexprPos | failure
    pure
      <DynamicEditButton 
          label={"Contrapose the implication"}
          range?={props.range} 
          insertion?={"lib_rewrite_rev contrapose " ++ (pos.toArray.toList).toString}
          vanish = {true} />
  else failure

/-- would be nice to have the contraposition step working for two selected expressions -/
@[motivated_proof_move]
def swap_hyps : InfoviewAction := fun props ↦ do
  if (props.selectedLocations.size == 1) then
    let some subexprPos := props.selectedLocations[0]? | failure
    let ⟨_, .target pos⟩ := subexprPos | failure
    pure
      <DynamicEditButton 
          label={"Rotate the hypotheses"}
          range?={props.range} 
          insertion?={"lib_rewrite Imp.swap " ++ (pos.toArray.toList).toString}
          vanish = {true} />
  else failure

lemma simple_inverse : ∃ f : ℤ → ℤ, ∀ n, f (n+1) = n := by
motivated_proof
tree_name m [1, 1, 2, 0, 1, 1]
lib_rewrite_rev eq_sub_iff_add_eq [1, 1, 1, 0, 2]
tree_rewrite [1, 1, 1, 0, 2, 0, 1] [1, 1, 1, 1, 2, 1]
lib_apply refl [1, 1, 2]

example : (α β : Type) → [PseudoMetricSpace α] →  [PseudoMetricSpace β] → (f : α → β) → (F : ℕ → α → β) →
  (∀ n, Continuous (F n)) → TendstoUniformly F f Filter.atTop → Continuous f := by
motivated_proof
lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] Metric.continuous_iff [1, 1, 1, 1, 1, 1, 0, 1, 2]
lib_rewrite [1, 1, 1, 1, 1, 1, 1, 2, 0, 1] Metric.tendstoUniformly_iff [1, 1, 1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 1, 1, 1, 2, 0, 1] Metric.continuous_iff [1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] Filter.eventually_atTop [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 2]
lib_rewrite_ord [1, 1, 1, 1, 1] dist_triangle [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
tree_rewrite_ord' [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 0, 1]
lib_rewrite_ord [1, 1, 1, 1, 1] dist_triangle [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] dist_comm [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1]
tree_rewrite_ord [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1]
tree_rewrite_ord [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 0, 1]
tree_apply [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
sorry


lemma Infinitude_of_Primes : ∀ n : ℕ, ∃ p : ℕ, n ≤ p ∧ Nat.Prime p := by
motivated_proof
lib_apply * [1, 1, 1, 0] Nat.exists_prime_and_dvd [1, 1, 1, 2]
lib_rewrite Imp.swap [1, 1, 1, 1]
lib_rewrite_rev contrapose [1, 1, 1, 1, 1]
lib_rewrite [1, 1, 2, 0, 1] Nat.not_le [1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 1, 2, 1] Nat.not_dvd_iff_between_consec_multiples [1, 1, 1, 1, 1, 1, 2]
tree_name pk [1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 0, 1]
lib_rewrite [1, 1, 2, 1] Nat.succ_le_iff [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
lib_apply  [1, 1, 1] Nat.le_of_eq [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2] 
tree_rewrite [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
tree_rewrite [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
lib_rewrite [1, 2, 1] Nat.add_one [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
-- some glue needed to make the two the same 
sorry


--in the new version I re-add the fact that p is prime, and I instantiate `n_1` as a successor.
lemma primes_continued : ∀ n : ℕ, ∃ n_1 : ℕ, n_1 ≠ 1 ∧ 
∀ p : ℕ,
Nat.Prime p → 
p < n → 
∃ k : ℕ, ∀ pk : ℕ,
p * k = pk → pk = n_1 ∧ 
n_1.succ < p * (k + 1) := by
motivated_proof
tree_rewrite [1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 0, 1]
tree_rewrite [1, 1, 1, 1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1]
lib_rewrite [1, 1, 1, 2, 0, 1] Nat.mul_add [1, 1, 1, 1, 1, 1, 1, 1, 2, 1]
lib_rewrite [1, 2, 1] Nat.add_one [1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
lib_rewrite [1, 1, 1, 2, 0, 1] Nat.add_lt_add_iff_left [1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 2, 0, 1] Nat.mul_one [1, 1, 1, 1, 1, 1, 1, 1, 2, 1]
lib_apply [1, 1] Nat.Prime.one_lt [1, 1, 1, 1, 1, 1, 1, 1, 2]
tree_apply [1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 1, 2]
lib_rewrite [1, 1, 2, 0, 1] Nat.mul_div_eq_iff_dvd [1, 1, 1, 1, 1, 1, 2]
tree_induction []
tree_simp [0, 1, 1, 1, 0, 2]
lib_apply [] Nat.zero_ne_one [0, 1, 2]
lib_rewrite [1, 1, 2, 0, 1] Nat.lt_add_one_iff [1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 2, 1] Nat.not_lt [1, 1, 1, 1, 1, 0, 2]
lib_rewrite [1, 1, 1, 1, 2, 0, 1] not_lt_iff_eq_or_lt [1, 1, 1, 1, 1, 0, 2]
tree_induction [1, 1, 1, 1, 1]
tree_rewrite_ord [1, 0, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 1, 2, 0, 1]
tree_apply [1, 1, 1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 1, 1, 1, 0, 2]
lib_apply [1, 1, 1, 0] Eq.symm [1, 1, 1, 1, 1, 1, 0, 0, 2]
tree_rewrite [1, 1, 1, 1, 1, 1, 0, 0, 2] [1, 1, 1, 1, 1, 1, 0, 1, 2, 0, 1]
lib_rewrite [1, 1, 1, 1, 1, 1, 2, 1] lcm_dvd_iff [1, 1, 1, 1, 1]
lib_apply refl [1, 1, 1, 1, 1, 2]
tree_simp []
tree_apply [1, 1, 0, 2] [1, 1, 1, 1, 2]
