import Lake
open Lake DSL System

package «leanTactics» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require webeditor from git
  "https://github.com/hhu-adam/lean4web-tools.git" @ "main"

@[default_target]
lean_lib MotivatedMoves

@[default_target]
lean_exe discrTrees where
  root := `MotivatedMoves.LibrarySearch.DiscrTreesData
  supportInterpreter := true

lean_lib Tests {
  globs := #[.submodules `Tests]
}
