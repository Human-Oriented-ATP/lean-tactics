import Tests.DiscrTrees.Main
import Lean

open Lean Elab Command Meta Tree

#eval show CommandElabM Unit from do
  let path ← cachePath
  _ ← path.parent.mapM fun p => IO.FS.createDirAll p
  pickle path (DiscrTree.dummyDiscrTree 1127) `DiscrTreesData

#eval DiscrTree.cachedData.format