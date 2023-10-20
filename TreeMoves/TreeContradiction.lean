import TreeMoves.TreeApply
import TreeMoves.TreeNormalize

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

elab "tree_contrapose" hypPos:treePos goalPos:treePos : tactic => do
  let (hypTreePos, hypPos) := getSplitPosition hypPos
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  workOnTree (applyBound hypTreePos goalTreePos hypPos goalPos true contrapose false)


example : (¬ p → q) → (¬ p → q) := by
  make_tree
  tree_contrapose [1,0] [1,1]
  tree_apply [0,1] [1,0,1]
  tree_push_neg [0]
  tree_apply [0] [1]