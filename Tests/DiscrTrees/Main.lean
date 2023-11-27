import Lean
import MotivatedMoves.LibrarySearch.LibrarySearch
import Std.Util.Pickle

open Lean Tree

namespace DiscrTree

def cachePath : IO System.FilePath := do
  try
    return (← findOLean `LibrarySearch.DiscrTreesData).withExtension "extra"
  catch _ =>
    return "build" / "lib" / "LibrarySearch" / "DiscrTreesData.extra"

def dummyDiscrTree (n : Nat) : DiscrTree Nat := 
  DiscrTree.insertInDiscrTree .empty #[.const `dummy 0] n

def buildData : IO (DiscrTree Nat) := do
  IO.sleep 1000
  IO.FS.writeFile "build/lib/LibrarySearch/debug.txt" "building data"
  return dummyDiscrTree 10

initialize cachedData : DiscrTree Nat ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle (DiscrTree Nat) path
    return d
  else
    buildData

end DiscrTree