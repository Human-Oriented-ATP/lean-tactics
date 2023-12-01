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

def dummyDiscrTree (a : α) [BEq α] : DiscrTree α := 
  DiscrTree.insertInDiscrTree .empty #[.const `dummy 0] a

def buildData : IO (DiscrTree LibraryLemma) := do
  IO.sleep 1000
  IO.FS.writeFile "build/lib/LibrarySearch/debug.txt" "building data"
  return dummyDiscrTree (LibraryLemma.mk `flt [0] [1] (.cons .root .wasChanged .nil))

initialize cachedData : DiscrTree LibraryLemma ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle (DiscrTree LibraryLemma) path
    return d
  else
    buildData

end DiscrTree