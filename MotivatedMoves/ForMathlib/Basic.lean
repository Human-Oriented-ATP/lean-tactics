import Lean
import ProofWidgets

open Lean Server ProofWidgets Elab Tactic

section

syntax location := " at" (term <|> "⊢") " position " str

def Lean.SubExpr.GoalLocation.ofLocation : TSyntax ``location → TacticM SubExpr.GoalLocation
  | `(location| at ⊢ position $pos:str) => return .target (.fromString! pos.getString)
  | `(location| at $hyp:term position $pos:str) => do
    let fvarId ← getFVarId hyp
    return .hypType fvarId (.fromString! pos.getString)
  |  _ => failure

end

structure InteractiveTacticProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
deriving RpcEncodable