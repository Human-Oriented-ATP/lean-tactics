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

section Scripts

open System

partial def moduleNamesIn (dir : FilePath) (ext := "lean") : IO (Array Name) :=
  dir.readDir >>= Array.concatMapM fun entry ↦ do
    if (← entry.path.isDir) then
      let n := entry.fileName.toName
      let mods ← Array.map (n ++ ·) <$> moduleNamesIn entry.path ext
      if mods.isEmpty then
        return #[]
      else
        return mods.push n
    else if entry.path.extension == some ext then
      return #[FilePath.withExtension entry.fileName "" |>.toString.toName]
    else return #[]

def importsForLib (dir : FilePath) (root : Name) : IO String := do
  moduleNamesIn (dir / root.toString) >>=
    Array.mapM (return .mkSimple root.toString ++ ·) >>=
    Array.foldlM (init := "") fun imports fileName ↦
      return imports ++ s!"import {fileName.toString}\n"

script import_all do
  let pkg ← Workspace.root <$> getWorkspace
  IO.println s!"Creating imports for package {pkg.name} ...\n"
  for lib in pkg.leanLibs do
    for root in lib.config.roots do
      let dir := lib.srcDir.normalize
      let fileName : FilePath := dir / (root.toString ++ ".lean")
      let imports ← importsForLib dir root
      IO.FS.writeFile fileName imports
      IO.println s!"Created imports file {fileName} for {root} library."
  return 0

script import_all? do
  let pkg ← Workspace.root <$> getWorkspace
  IO.println s!"Checking imports for package {pkg.name} ...\n"
  for lib in pkg.leanLibs do
    for root in lib.config.roots do
      let dir := lib.srcDir.normalize
      let fileName : FilePath := dir / (root.toString ++ ".lean")
      let allImports ← importsForLib dir root
      let existingImports ← IO.FS.readFile fileName
      unless existingImports == allImports do
        IO.eprintln s!"Invalid import list for {root} library."
        IO.eprintln s!"Try running `lake run mkImports`."
        return 1
  IO.println s!"The imports for package {pkg.name} are up to date."
  return 0

end Scripts