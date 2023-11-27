import Lean
import Std.Util.Pickle

open Lean

def cachePath : IO System.FilePath := do
  try
    return (← findOLean `LibrarySearch.DiscrTreesData).withExtension "extra"
  catch _ =>
    return "build" / "lib" / "LibrarySearch" / "DiscrTreesData.extra"

def buildData : IO Nat := do
  IO.sleep 1000
  IO.FS.writeFile "build/lib/LibrarySearch/debug.txt" "building data"
  return 102325346

initialize cachedData : Nat ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle Nat path
    return d
  else
    buildData