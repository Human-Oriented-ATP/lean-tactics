import Lake
open Lake DSL System

package «leanTactics» {
  -- add any package configuration options here
  precompileModules := true
  preferReleaseBuild := true
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

lean_lib Tree {
  -- add any library configuration options here
}

lean_lib PrintTree {
  -- add any library configuration options here
}

lean_lib TreeApply {
  -- add any library configuration options here
}

lean_lib TreeRewrite {
  -- add any library configuration options here
}

lean_lib TreeRewriteOrd {
  -- add any library configuration options here
}

lean_lib InfoDisplayTactics {
  -- add any library configuration options here
}

section Scripts

/-! A script to automatically generate top-level import files for each library. -/

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

section ProofWidgets

/-! Scripts from the `ProofWidgets` `lakefile` to build `TypeScript` code. -/

def npmCmd : String :=
  if Platform.isWindows then "npm.cmd" else "npm"

def widgetDir := __dir__ / "widget"

/-- Target to update `package-lock.json` whenever `package.json` has changed. -/
target widgetPackageLock : FilePath := do
  let packageFile ← inputFile <| widgetDir / "package.json"
  let packageLockFile := widgetDir / "package-lock.json"
  buildFileAfterDep packageLockFile packageFile fun _srcFile => do
    proc {
      cmd := npmCmd
      args := #["install"]
      cwd := some widgetDir
    }

/-- Target to build `build/js/foo.js` from a `widget/src/foo.tsx` widget module.
Rebuilds whenever the `.tsx` source, or any part of the build configuration, has changed. -/
def widgetTsxTarget (pkg : NPackage _package.name) (nodeModulesMutex : IO.Mutex Bool)
    (tsxName : String) (deps : Array (BuildJob FilePath)) (isDev : Bool) :
    IndexBuildM (BuildJob FilePath) := do
  let jsFile := pkg.buildDir / "js" / s!"{tsxName}.js"
  buildFileAfterDepArray jsFile deps fun _srcFile => do
    /-
    HACK: Ensure that NPM modules are installed before building TypeScript, *if* we are building it.
    It would probably be better to have a proper target for `node_modules`
    that all the `.tsx` modules depend on.
    BUT when we are being built as a dependency of another package using the cloud releases feature,
    we wouldn't want that target to trigger since in that case NPM is not necessarily installed.
    Hence we put this block inside the build process for any `.tsx` file
    rather than as a top-level target.
    This only runs when some TypeScript needs building.
    It has to be guarded by a mutex to avoid multiple `.tsx` builds trampling on each other
    with multiple `npm clean-install`s.
    -/
    nodeModulesMutex.atomically (m := IO) do
      if (← get) then return
      let _ ← IO.Process.run {
        cmd := npmCmd
        args := #["clean-install"]
        cwd := some widgetDir
      }
      set true
    proc {
      cmd := npmCmd
      args :=
        if isDev then
          #["run", "build-dev", "--", "--tsxName", tsxName]
        else
          #["run", "build", "--", "--tsxName", tsxName]
      cwd := some widgetDir
    }

/-- Target to build all TypeScript widget modules that match `widget/src/*.tsx`. -/
def widgetJsAllTarget (pkg : NPackage _package.name) (isDev : Bool) :
    IndexBuildM (BuildJob (Array FilePath)) := do
  let fs ← (widgetDir / "src").readDir
  let tsxs : Array FilePath := fs.filterMap fun f =>
    let p := f.path; if let some "tsx" := p.extension then some p else none
  -- Conservatively, every .js build depends on all the .tsx source files.
  let depFiles := tsxs ++ #[ widgetDir / "rollup.config.js", widgetDir / "tsconfig.json" ]
  let deps ← liftM <| depFiles.mapM inputFile
  let deps := deps.push $ ← fetch (pkg.target ``widgetPackageLock)
  let nodeModulesMutex ← IO.Mutex.new false
  let jobs ← tsxs.mapM fun tsx => widgetTsxTarget pkg nodeModulesMutex tsx.fileStem.get! deps isDev
  BuildJob.collectArray jobs

def customTsxTargetFilePath : FilePath :=
  widgetDir / "tsx-target.txt"

def customTsxFilePath : IO FilePath := do
  let tsxFileName : FilePath := ⟨(← IO.FS.readFile customTsxTargetFilePath).trim⟩
  unless tsxFileName.extension = some "tsx" do
    throw <| IO.userError
      s!"The file {tsxFileName} in {customTsxTargetFilePath} does not have the `.tsx` extension."
  return widgetDir / "src" / tsxFileName

/-- A version of `widgetJsAllTarget` that builds a single standalone `.tsx` file
   whose name is specified in the `./widget/tsx-target.txt` file. -/
def customWidgetJsTarget (pkg : NPackage _package.name) (isDev : Bool) :
    IndexBuildM (BuildJob (Array FilePath)) := do
  let tsx ← customTsxFilePath
  let depFiles := #[ widgetDir / "rollup.config.js", widgetDir / "tsconfig.json" ]
  let deps ← liftM <| depFiles.mapM inputFile
  let deps := deps.push $ ← fetch (pkg.target ``widgetPackageLock)
  let nodeModulesMutex ← IO.Mutex.new false
  let tsxFileStem := tsx.fileStem.get!
  IO.println s!"Building JavaScript file for {tsxFileStem}..."
  let jsFile := pkg.buildDir / "js" / s!"{tsxFileStem}.js"
  let jsFileTrace := pkg.buildDir / "js" / s!"{tsxFileStem}.js.trace"
  if (← jsFile.pathExists) && (← jsFileTrace.pathExists) then
    IO.println "Removing previous builds ..."
    IO.FS.removeFile jsFile
    IO.FS.removeFile jsFileTrace
  else IO.println "No previous builds to remove. Starting afresh ..."
  let job ← widgetTsxTarget pkg nodeModulesMutex tsxFileStem deps isDev
  BuildJob.collectArray #[job]

target customWidgetJs (pkg : NPackage _package.name) : Array FilePath := do
  customWidgetJsTarget pkg (isDev := true)

target widgetJsAll (pkg : NPackage _package.name) : Array FilePath := do
  widgetJsAllTarget pkg (isDev := false)

target widgetJsAllDev (pkg : NPackage _package.name) : Array FilePath := do
  widgetJsAllTarget pkg (isDev := true)

@[default_target]
target all (pkg : NPackage _package.name) : Unit := do
  let some lib := pkg.findLeanLib? ``LeanTactics |
    error "Cannot find lean_lib target {LeanTactics}."
  let job₁ ← fetch (pkg.target ``widgetJsAll)
  let _ ← job₁.await
  let job₂ ← lib.recBuildLean
  let _ ← job₂.await
  return .nil

end ProofWidgets