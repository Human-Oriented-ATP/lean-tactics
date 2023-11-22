import MotivatedMoves.LibrarySearch.LibrarySearch
-- import Mathlib

open Lean Elab Command Tree

run_cmd liftTermElabM do
  let path ← cachePath
  _ ← path.parent.mapM fun p => IO.FS.createDirAll p
  pickle path (← buildDiscrTrees) `DiscrTreesData