import Lake
open Lake DSL

package «lean4» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Lean4» {
  -- add any library configuration options here
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

lean_lib InfoDisplayTactics {
  -- add any library configuration options here
}