import Tests.DiscrTrees.Main
import Lean

open Lean Elab Command Meta

#eval show CommandElabM Unit from do
  let path ← cachePath
  _ ← path.parent.mapM fun p => IO.FS.createDirAll p
  pickle path 5 `DiscrTreesData

#eval cachedData