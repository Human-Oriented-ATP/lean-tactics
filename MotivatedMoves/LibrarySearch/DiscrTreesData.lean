import MotivatedMoves.LibrarySearch.LibrarySearch
import Mathlib

open Lean Elab Command MotivatedTree

def main (args : List String) : IO Unit := do
  let path ← cachePath

  if ← path.pathExists then
    unless args = ["--force"] do
      IO.println s!"The cache already appears to be stored at {path}."
      IO.println "Retaining existing cache and exiting ..."
      return ()
    IO.println "Regenerating cache ..."

  IO.FS.createDirAll path.parent.get!

  initSearchPath (← Lean.findSysroot) [
    "build/lib",
    "lake-packages/mathlib/build/lib/",
    "lake-packages/std/build/lib/",
    "lake-packages/Qq/build/lib/",
    "lake-packages/aesop/build/lib/",
    "lake-packages/proofwidgets/build/lib"
    ]
  let env ← importModules #[{ module := `Mathlib }] .empty
  let out := pickleDiscrTrees path
    |>.run' {}
    |>.run' {fileName := "", fileMap := default} { env := env }
  match ← out.toIO' with
  | .ok _ => IO.println "\nWritten `DiscrTrees` to file."
  | .error e => IO.throwServerError <| ← e.toMessageData.toString
where
  pickleDiscrTrees (path : System.FilePath) : MetaM Unit := do
    pickle path (← getLibraryLemmas).2 `DiscrTreesData
