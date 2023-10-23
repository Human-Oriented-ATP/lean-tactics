import MotivatedMoves.Moves.TreeApply
import MotivatedMoves.Moves.TreeInduction
import MotivatedMoves.Moves.TreeNaming
import MotivatedMoves.Moves.TreeNormalize
import MotivatedMoves.Moves.TreeRewrite
import MotivatedMoves.Moves.TreeRewriteDef
import MotivatedMoves.Moves.TreeRewriteOrd
import MotivatedMoves.Moves.TreeSearch
import MotivatedMoves.Moves.TreeContradiction

namespace Tree

lemma forall_exists_unify (p : α → α → Prop) : (∀ a, p a a) → ∀ a, ∃ b, p a b :=
  fun h a => ⟨a, h a⟩

macro "unify_forall_exists" pos:treePos : tactic => `(tactic| lib_apply [1,1,1] $(Lean.mkIdent ``forall_exists_unify) $pos)
