import Tests.DiscrTrees.Main
import Lean

open Lean Elab Command Meta Tree

#eval show CommandElabM Unit from do
  let path ← cachePath
  _ ← path.parent.mapM fun p => IO.FS.createDirAll p
  pickle path (DiscrTree.dummyDiscrTree (LibraryLemma.mk `riemann_hyp [0, 1] [1, 1] (.cons .root .wasChanged .nil))) `DiscrTreesData

#eval DiscrTree.cachedData.format