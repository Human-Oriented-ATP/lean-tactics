import Implementations

lemma FirstIsomorphismTheorem {G : Type u} [group G] {H : Type v} [group H] (φ : G →* H) :
  G ⧸ φ.ker ≃* ↥(φ.range) := by
