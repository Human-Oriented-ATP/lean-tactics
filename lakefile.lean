import Lake
open Lake DSL

package «leanTactics» {
  -- add any package configuration options here
  precompileModules := true
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require pointAndClick from git 
  "https://github.com/MantasBaksys/PointAndClick.git"

@[default_target]
lean_lib «LeanTactics» {
  -- add any library configuration options here
}

@[default_target]
lean_exe «leanTactics» {
  root := `LeanTactics
  supportInterpreter := true
}

lean_lib Tidying {
  -- add any library configuration options here
}

lean_lib Skolem {
  -- add any library configuration options here
}

lean_lib Implementations {
  -- add any library configuration options here
}

lean_lib RewriteExperiments {
  -- add any library configuration options here
}

lean_lib RewriteOrd {
  -- add any library configuration options here
}

lean_lib InfoDisplayTactics {
  -- add any library configuration options here
}