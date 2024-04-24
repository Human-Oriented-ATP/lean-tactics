import MotivatedMoves.Moves.TreeApply
import MotivatedMoves.Moves.TreeNormalize

namespace Tree
open Lean Meta Elab Tactic

lemma tree_contrapose {p q : Prop} (h : p) : (¬ q → ¬ p) → q := (not_imp_not.mp · h)

def contrapose (hypContext : HypothesisContext) (hyp goal : Expr) (pol : Bool) (hypOuterPosition : OuterPosition) (hypPos goalPos : InnerPosition) : MetaM' TreeProof := do
  unless hypPos == [] && hypOuterPosition == [] do
    throwError m! "cannot contrapose a subexpression: position {hypPos} in {hyp}"
  unless goalPos == [] do
    throwError m! "cannot contrapose in a subexpression: position {goalPos} in {goal}"
  unless pol do
    throwError m! "cannot contrapose in negative position"
  let {metaIntro, instMetaIntro, hypProofM} := hypContext
  _ ← metaIntro
  let instMVars ← instMetaIntro
  -- no unification needed here
  synthMetaInstances instMVars
  let (hyp, proof) ← hypProofM
  let result : TreeProof := {
    newTree := mkImp (mkNot goal) (mkNot hyp)
    proof := mkApp3 (.const ``tree_contrapose []) hyp goal proof }
  result.map (simpMove (← pushNegContext) none [] pol) pol goal

/- Contrapose hypothesis `H`, replacing the target `T` with `¬ T ⇨ ¬ H`.
This also pushes the negations through and deletes hypothesis `H`.
For a version that remembers `H`, see `tree_contrapose'`. -/
elab "tree_contrapose" hypPos:treePos goalPos:treePos : tactic => do
  let (hypOuterPosition, hypPos) := getOuterInnerPosition hypPos
  let (goalOuterPosition, goalPos) := getOuterInnerPosition goalPos
  workOnTree (applyBound hypOuterPosition goalOuterPosition hypPos goalPos true contrapose false)

/- Contrapose hypothesis `H`, replacing the target `T` with `¬ T ⇨ ¬ H`.
This also pushes the negations through and remembers `H` -/
elab "tree_contrapose'" hypPos:treePos goalPos:treePos : tactic => do
  let (hypOuterPosition, hypPos) := getOuterInnerPosition hypPos
  let (goalOuterPosition, goalPos) := getOuterInnerPosition goalPos
  workOnTree (applyBound hypOuterPosition goalOuterPosition hypPos goalPos false contrapose false)

open scoped ProofWidgets.Jsx in
@[new_motivated_proof_move]
def treeContraposeMove : MotivatedProof.Suggestion
  | #[pos₁, pos₂] => do
    let tac ← `(tactic| tree_contrapose $(quote pos₁) $(quote pos₂))
    let _ ← OptionT.mk <| withoutModifyingState <|
      try? <| evalTactic tac
    return {
      description := "Contrapose",
      code := do
        let keepHyp ← askUserBool 0 <p>Would you like to keep the selected hypothesis?</p>
        return s!"tree_contrapose{if keepHyp then "" else "'"} {pos₁} {pos₂}"
    }
  | _ => failure
