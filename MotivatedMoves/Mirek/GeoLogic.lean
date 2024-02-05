import Lean.Widget
import ProofWidgets
import MotivatedMoves.Mirek.GeoConstr
-- import ProofWidgets.Component.HtmlDisplay

open Lean Widget ProofWidgets
open ProofWidgets.Jsx

structure GeoLogicProps
deriving ToJson, FromJson

@[widget_module]
def GeoLogic : Component GeoLogicProps where
  javascript := include_str ".." / ".." / "build" / "js" / "geoLogic.js"

#html <GeoLogic />

namespace GeoLogic

elab "hi" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  let steps ← GeoLogic.testRef.get
  logInfo m! "{GeoLogic.stepsToTerm.aux steps GeoLogic.stepsToTerm.Context.empty}"

end GeoLogic

/-
∀ (A B C : Point) (ω : Circle), isCircumCircle ω A B C →
-/
