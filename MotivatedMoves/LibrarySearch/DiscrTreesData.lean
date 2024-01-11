import MotivatedMoves.LibrarySearch.LibrarySearch
import Mathlib

open Lean Elab Command Tree

def main : IO Unit := do
  let path ← cachePath
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  if ← path.pathExists then
    stdout.putStrLn s!"The cache already appears to be stored at {path}.\nWould you like to rewrite it? (y / n)"
    let input ← stdin.getLine
    unless input.trim = "y" do
      stdout.putStrLn "Retaining existing cache and exiting ..."
      return ()
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
  | .ok _ => stdout.putStrLn "\nWritten `DiscrTrees` to file."
  | .error e => IO.throwServerError <| ← e.toMessageData.toString 
where
  pickleDiscrTrees (path : System.FilePath) : MetaM Unit := do
    pickle path (← getLibraryLemmas).2 `DiscrTreesData