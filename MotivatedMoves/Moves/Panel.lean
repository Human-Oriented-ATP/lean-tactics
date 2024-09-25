import MotivatedMoves.Moves.Basic
import MotivatedMoves.GUI.SVGTree
import ProofWidgets

open Lean Meta Elab Term Tactic ProofWidgets Server Jsx Json

namespace MotivatedProof

structure MotivatedProofPanelProps extends PanelWidgetProps where
  selections : Array SubExpr.Pos
  range : Lsp.Range
deriving RpcEncodable

def suggestMotivatedMoves (selections : Array SubExpr.Pos) (indent : Nat) : TacticIM Unit := do
  let suggestions := suggestionExt.getState (← getEnv)
  let moves : Array Move ← suggestions.filterMapM <|
      fun (_, suggestion) ↦ (suggestion selections).run
  let motivatedMoveChoice ← askUserSelect 0
    <div>Motivated proof moves</div>
    (moves.map fun ⟨description, code⟩ ↦ (code, <button>{.text description}</button>)).toList
  let tactic ← motivatedMoveChoice
  insertLine <| ("".pushn ' ' indent) ++ tactic

@[server_rpc_method]
def MotivatedProofMovePanel.rpc (props : MotivatedProofPanelProps) : RequestM (RequestTask Html) := do
  let some goal := props.goals[0]? | return .pure <span>No goals found</span>
  goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let currentCode : TacticIM Unit := do
        initEdit props.range.end
        suggestMotivatedMoves (indent := props.range.start.character + 2) props.selections
      let (rawCode, _) ← TermElabM.run' <| currentCode.run { elaborator := .anonymous }
                          |>.run { goals := [goal.mvarId] }
      return .pure <ProgWidget code={rawCode} key={toString props.selections} />

syntax (name := motivatedProofMode) "motivated_proof" tacticSeq : tactic

-- Optional TODO: Synchronize the widget output with the current cursor position using `InfoTree`s
@[tactic motivatedProofMode]
def motivatedProofModeImpl : Tactic
  | stx@`(tactic| motivated_proof $seq) => withMainContext do
    let some range := (← getFileMap).rangeOfStx? stx | return
    -- this turns the goal into a tree initially
    MotivatedTree.workOnTreeDefEq pure
    evalTacticSeq seq
    if (← getUnsolvedGoals).isEmpty then
      logInfo "Goals accomplished 🎉\nThe proof tree is rendered only when there are open goals left."
    else do
      let e ← getMainTarget
      let (t, _) ← MotivatedTree.toDisplayTree
            |>.run { optionsPerPos := ∅, currNamespace := (← getCurrNamespace), openDecls := (← getOpenDecls), subExpr := ⟨e, .root⟩ }
            |>.run {}
      Widget.savePanelWidgetInfo (hash RenderTree.javascript) (stx := stx) do
        return json% {
          tree : $( ← rpcEncode (WithRpcRef.mk t) ),
          selections: $( (.empty : Array SubExpr.Pos) ),
          range: $( range ) }
  | _ => throwUnsupportedSyntax

end MotivatedProof
