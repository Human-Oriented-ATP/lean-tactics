import LeanTactics.DynamicButton
import TreeMoves.TreeRewrite
import TreeMoves.TreeRewriteOrd

open ProofWidgets Lean Meta

open scoped Jsx
open OptionT

@[motivated_proof_move]
def treeApplyButton : InfoviewAction := 
  fun props => do
  let panelProps := props.toPanelWidgetProps
  if (panelProps.selectedLocations.size == 2) then
    let subexprPos := panelProps.selectedLocations
    let some pos1 := subexprPos[0]? | OptionT.fail
    let some pos2 := subexprPos[1]? | OptionT.fail
    let ⟨_, .target subexprPos1⟩  := pos1 | OptionT.fail
    let ⟨_, .target subexprPos2⟩ := pos2 | OptionT.fail
    let text := "tree_apply " ++ 
                  ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ 
                  ((SubExpr.Pos.toArray subexprPos2).toList).toString
    pure <DynamicEditButton 
            label={"Tree apply at"} 
            range?={props.range} 
            insertion?={text} 
            html?={<p> Applying... </p>}
            vanish={true} />
  else OptionT.fail

@[motivated_proof_move]
def treeRewriteAtButton : InfoviewAction := 
  fun props => do
  let panelProps := props.toPanelWidgetProps
  if (panelProps.selectedLocations.size == 2) then
    let subexprPos := panelProps.selectedLocations
    let some pos1 := subexprPos[0]? | OptionT.fail
    let some pos2 := subexprPos[1]? | OptionT.fail
    let ⟨_, .target subexprPos1⟩ := pos1 | OptionT.fail
    let ⟨_, .target subexprPos2⟩ := pos2 | OptionT.fail
    let text := ("tree_rewrite " ++ 
              ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ 
              ((SubExpr.Pos.toArray subexprPos2).toList).toString)
    pure <DynamicEditButton 
            label={"Tree rewrite at"} 
            range?={props.range} 
            insertion?={text} 
            html?={<p> Rewriting... </p>}
            vanish={true} />
  else OptionT.fail

-- @[motivated_proof_move]
-- def simpButton : InfoviewAction := 
--   fun props => do
--     pure 
--       <DynamicEditButton 
--         label={"Try `simp`"} 
--         range?={props.range} 
--         insertion?={"simp"} 
--         html?={<p> Simplifying the target... </p>}
--         vanish={true} />

@[motivated_proof_move]
def treeSimp : InfoviewAction := 
  fun props => do
    let panelProps := props.toPanelWidgetProps
    if (panelProps.selectedLocations.size == 1) then
      let some pos := panelProps.selectedLocations[0]? | OptionT.fail
      let ⟨_, .target subexprPos⟩ := pos | OptionT.fail
      let text := "tree_simp " ++ ((SubExpr.Pos.toArray subexprPos).toList).toString
      pure 
        <DynamicEditButton 
          label={"Try to simplify the selected subexpression"} 
          range?={props.range} 
          insertion?={text} 
          html?={<p> Simplifying the target... </p>}
          vanish={true} />
    else OptionT.fail

@[motivated_proof_move]
def make_tree : InfoviewAction :=
  fun props => do
    pure 
      <DynamicEditButton 
        label={"Turn the tactic state into a tree"} 
        range?={props.range} 
        insertion?={"make_tree"}
        html?={<p> Making a tree... </p>}
        vanish={true} />

@[motivated_proof_move]
def tree_rewrite_ord : InfoviewAction := 
  fun props => do 
    let panelProps := props.toPanelWidgetProps
    if (panelProps.selectedLocations.size == 2) then 
      let subexprPos := panelProps.selectedLocations
      let some pos1 := subexprPos[0]? | OptionT.fail
      let some pos2 := subexprPos[1]? | OptionT.fail
      let ⟨_, .target subexprPos1⟩ := pos1 | OptionT.fail
      let ⟨_, .target subexprPos2⟩ := pos2 | OptionT.fail
      let text := ("tree_rewrite_ord " ++ 
              ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ 
              ((SubExpr.Pos.toArray subexprPos2).toList).toString)
      pure <DynamicEditButton 
            label={"Ordered tree rewrite at"} 
            range?={props.range} 
            insertion?={text} 
            html?={<p> Rewriting... </p>}
            vanish={true} />        
    else OptionT.fail

@[motivated_proof_move]
def tree_search : InfoviewAction := 
  fun props => do 
    pure <DynamicEditButton 
            label={"Search the tree for redundant hypotheses & goals"} 
            range?={props.range} 
            insertion?={"tree_search"} 
            html?={<p> Searching the tree... </p>}
            vanish={true} />  

@[motivated_proof_move]
def tree_induction : InfoviewAction := 
  fun props => do 
    let panelProps := props.toPanelWidgetProps
    if (panelProps.selectedLocations.size == 1) then
      let some pos := panelProps.selectedLocations[0]? | OptionT.fail
      let ⟨_, .target subexprPos⟩ := pos | OptionT.fail
      let text := "tree_induction" ++ ((SubExpr.Pos.toArray subexprPos).toList).toString
      pure 
        <DynamicEditButton 
          label={"Apply induction on the selected subexpression"} 
          range?={props.range} 
          insertion?={text} 
          html?={<p> Performing induction... </p>}
          vanish={true} />
    else OptionT.fail

@[motivated_proof_move]
def lib_rewrite : InfoviewAction :=
  fun props => do 
    let panelProps := props.toPanelWidgetProps
    if (panelProps.selectedLocations.size == 1) then
      let some pos := panelProps.selectedLocations[0]? | OptionT.fail
      let ⟨_, .target subexprPos⟩ := pos | OptionT.fail
      let text := "lib_rewrite" ++ ((SubExpr.Pos.toArray subexprPos).toList).toString
      -- below
      pure 
        <DynamicEditButton 
          label={"Library rewrite at a selected position (to be implemented)"} 
          range?={props.range} 
          insertion?={text} 
          html?={<p> Rewriting... </p>}
          vanish={true} />
    else OptionT.fail

-- TODO: Move

open Widget

def mkDiv: Array Html → Html := 
  .element "div" #[]

def mkFragment : Array Html → Html :=
  .element "" #[]

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
    return mkFragment 
      #[ <DynamicEditButton label={name.toString} range?={range} insertion?={text} />, 
          ← name.renderWithDiffs diffs ]

open Jsx in
@[motivated_proof_move]
def libRewrite : InfoviewAction := fun props ↦ do
  let #[⟨goal, .target pos⟩] := props.selectedLocations | OptionT.fail
  let libSuggestions ← Tree.librarySearchRewrite pos.toArray.toList (← goal.getType)
  pure
    <DynamicEditButton 
        label={"Rewrite with library result"} 
        html?={← renderLibrarySearchResults props.range "Library rewrite results" libSuggestions} />
  
lemma temp (h : 1 = 1) : 1 = 1 ∧ 1 = 2 := by
motivated_proof
  
skip




