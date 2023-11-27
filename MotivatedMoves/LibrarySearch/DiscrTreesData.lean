import MotivatedMoves.LibrarySearch.LibrarySearch
import Mathlib

open Lean Elab Command Tree

def storeDiscrTrees : MetaM Unit := do
  let path ← cachePath
  IO.FS.createDirAll path.parent.get!
  pickle path (← getLibraryLemmas).2 `DiscrTreesData

def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) [
    "build/lib", 
    "lake-packages/mathlib/build/lib/",  
    "lake-packages/std/build/lib/", 
    "lake-packages/Qq/build/lib/", 
    "lake-packages/aesop/build/lib/", 
    "lake-packages/proofwidgets/build/lib"
    ]
  let env ← importModules  #[{ module := `Mathlib }] .empty
  let out := storeDiscrTrees
    |>.run' {} 
    |>.run' {fileName := "", fileMap := default} { env := env }
  match ← out.toIO' with
  | .ok _ => IO.println "Written `DiscrTrees` to file."
  | .error e => IO.throwServerError <| ← e.toMessageData.toString 