import MotivatedMoves.Moves.TreeApply
import MotivatedMoves.Moves.TreeNormalize

namespace Tree
open Lean Meta

lemma tree_contrapose {p q : Prop} (h : p) : (¬ q → ¬ p) → q := (not_imp_not.mp · h)

def contrapose (hypContext : HypothesisContext) (hyp goal : Expr) (pol : Bool) (hypTreePos : TreePos) (hypPos goalPos : Pos) : MetaM' TreeProof := do
  unless hypPos == [] && hypTreePos == [] do    
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
  let (hypTreePos, hypPos) := getSplitPosition hypPos
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  workOnTree (applyBound hypTreePos goalTreePos hypPos goalPos true contrapose false)

/- Contrapose hypothesis `H`, replacing the target `T` with `¬ T ⇨ ¬ H`.
This also pushes the negations through and remembers `H` -/
elab "tree_contrapose'" hypPos:treePos goalPos:treePos : tactic => do
  let (hypTreePos, hypPos) := getSplitPosition hypPos
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  workOnTree (applyBound hypTreePos goalTreePos hypPos goalPos false contrapose false)
