import LeanTactics.DynamicButton

open ProofWidgets Lean Meta

open scoped Jsx

@[motivated_proof_move]
def treeApplyButton : InfoviewAction := 
  fun props => do
  let panelProps := props.toPanelWidgetProps
  if (panelProps.selectedLocations.size == 2) then
    let subexprPos := panelProps.selectedLocations
    let some pos1 := subexprPos[0]? | throwError "You need to select an expression"
    let some pos2 := subexprPos[1]? | throwError "You need to select an expression"
    let ⟨_, .target subexprPos1⟩  := pos1 | throwError "Your selected expression should be in the target"
    let ⟨_, .target subexprPos2⟩ := pos2 | throwError "Your selected expression should be in the target"
    return some (.text ("tree_apply " ++ 
                  ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ 
                  ((SubExpr.Pos.toArray subexprPos2).toList).toString))
  else return none

@[motivated_proof_move]
def treeRewriteAtButton : InfoviewAction := 
  fun props => do
  let panelProps := props.toPanelWidgetProps
  if (panelProps.selectedLocations.size == 2) then
    let subexprPos := panelProps.selectedLocations
    let some pos1 := subexprPos[0]? | throwError "You must select something."
    let some pos2 := subexprPos[1]? | throwError "You must select something."
    let ⟨_, .target subexprPos1⟩ := pos1 | throwError "You must select something in the goal."
    let ⟨_, .target subexprPos2⟩ := pos2 | throwError "You must select something in the goal."
    return some (.text ("tree_rewrite " ++ 
              ((SubExpr.Pos.toArray subexprPos1).toList).toString ++ " " ++ 
              ((SubExpr.Pos.toArray subexprPos2).toList).toString))
  else return none

@[motivated_proof_move]
def simpButton : InfoviewAction := 
  fun _ => do return some (.text "try simp")



