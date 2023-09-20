import LeanTactics.DynamicButton

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
      let text := "tree_simp" ++ ((SubExpr.Pos.toArray subexprPos).toList).toString
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
          html?={<p> Simplifying the target... </p>}
          vanish={true} />
    else OptionT.fail
  
example : 1 = 1 := by
  motivated_proof
    skip
    simp
    
