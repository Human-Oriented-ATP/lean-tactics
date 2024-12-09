import Lake
open Lake DSL System

package «leanTactics» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.13.0"

require webeditor from git
  "https://github.com/hhu-adam/lean4web-tools.git" @ "main"

require verso from git "https://github.com/leanprover/verso" @ "v4.13.0"

-- require leanaide from git "https://github.com/siddhartha-gadgil/LeanAide" @ "main"

@[default_target]
lean_lib MotivatedMoves

@[default_target]
lean_exe discrTrees where
  root := `MotivatedMoves.LibrarySearch.DiscrTreesData
  supportInterpreter := true

lean_lib Tests {
  globs := #[.submodules `Tests]
}

lean_exe demo where
  srcDir := "MotivatedMoves/AutoGeneralization/Demo"
  root := `Main
  supportInterpreter := true
