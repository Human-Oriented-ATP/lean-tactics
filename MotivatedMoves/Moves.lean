import MotivatedMoves.Moves.TreeApply
import MotivatedMoves.Moves.TreeInduction
import MotivatedMoves.Moves.TreeNaming
import MotivatedMoves.Moves.TreeNormalize
import MotivatedMoves.Moves.TreeRewrite
import MotivatedMoves.Moves.TreeRewriteDef
import MotivatedMoves.Moves.TreeRewriteOrd
import MotivatedMoves.Moves.TreeSearch
import MotivatedMoves.Moves.TreeContradiction

open Lean Elab Tactic

namespace Tree

lemma forall_exists_unify (p : α → α → Prop) : (∀ a, p a a) → ∀ a, ∃ b, p a b :=
  fun h a => ⟨a, h a⟩

macro "unify_forall_exists" pos:treePos : tactic => `(tactic| lib_apply [1,1,1] $(Lean.mkIdent ``forall_exists_unify) $pos)

@[new_motivated_proof_move]
def treeUnifyForallExistsMove : MotivatedProof.Suggestion
  | #[pos] => do
    let tac ← `(tactic| unify_forall_exists $(quote pos))
    let _ ← OptionT.mk <| withoutModifyingState <|
      try? <| evalTactic tac
    return {
      description := "Unify existential with preceding universal variable",
      code := return s!"unify_forall_exists {pos}"
    }
  | _ => failure
