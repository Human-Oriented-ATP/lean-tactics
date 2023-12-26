import MotivatedMoves.LibrarySearch.DiscrTree

namespace Tree

open RefinedDiscrTree Lean Meta

inductive LibraryLemmaKind where
| apply
| apply_rev
| rewrite
| rewrite_ord
| rewrite_ord_rev
deriving BEq

structure LibraryLemma where
  name : Name
  treePos : OuterPosition
  pos : InnerPosition
  diffs : AssocList SubExpr.Pos Widget.DiffTag

instance : BEq LibraryLemma where
  beq := fun {name, pos, ..} {name := name', pos := pos', ..} => name == name' && pos == pos'
instance : ToFormat LibraryLemma where
  format := (toString ·.name)



structure DiscrTrees where
  apply           : RefinedDiscrTree LibraryLemma := {}
  apply_rev       : RefinedDiscrTree LibraryLemma := {}
  rewrite         : RefinedDiscrTree LibraryLemma := {}
  rewrite_ord     : RefinedDiscrTree LibraryLemma := {}
  rewrite_ord_rev : RefinedDiscrTree LibraryLemma := {}

instance : Inhabited DiscrTrees := ⟨{}⟩

structure ProcessResult where
  apply           : Array (AssocList OuterPosition Widget.DiffTag × OuterPosition × InnerPosition × List DTExpr) := #[]
  apply_rev       : Array (AssocList OuterPosition Widget.DiffTag × OuterPosition × InnerPosition × List DTExpr) := #[]
  rewrite         : Array (AssocList OuterPosition Widget.DiffTag × OuterPosition × InnerPosition × List DTExpr) := #[]
  rewrite_ord     : Array (AssocList OuterPosition Widget.DiffTag × OuterPosition × InnerPosition × List DTExpr) := #[]
  rewrite_ord_rev : Array (AssocList OuterPosition Widget.DiffTag × OuterPosition × InnerPosition × List DTExpr) := #[]
instance : Append ProcessResult where
  append := (fun ⟨a, b, c, d, e⟩ ⟨a',b',c',d',e'⟩ => ⟨a++a',b++b',c++c',d++d',e++e'⟩)

-- might want to add some whnf applications with reducible transparency?
partial def processTree (name : Name): Expr → MetaM ProcessResult
  | .forallE _n domain body bi => do
    let mvar ← mkFreshExprMVar domain
    let result ← processTree name (body.instantiate1 mvar)

    if bi.isInstImplicit
    then
      return addBinderKind [1] 1 result
    else
      let u ← getLevel domain
      if ← pure !body.hasLooseBVars <&&> isLevelDefEq u .zero
      then
        let result := addBinderKind [1] 1 result
        return { result with apply_rev := result.apply_rev.push (AssocList.nil.cons [0] .willChange |>.cons [1] .wasChanged, [0], [], ← mkDTExprs domain) }
      else
        return addBinderKind [1] 1 result

  | regular_exists_pattern n _u d body _ =>
    withLocalDeclD n d fun fvar =>
    addBinderKind [1,1] 1 <$> processTree name (body.instantiate1 fvar)

  | regular_and_pattern p q =>
    return (← addBinderKind [0,1] 0 <$> processTree name p) ++ (← addBinderKind [1] 1 <$> processTree name q)

  | e => do
    let mut result : ProcessResult := {}
    match e with
    | .app (.app (.app (.const ``Eq _) _) lhs) rhs
    | .app (.app (.const ``Iff _) lhs) rhs =>
      result := { result with rewrite := result.rewrite.push (AssocList.nil.cons [0,1] .willChange |>.cons [1] .wasChanged, [], [0,1], ← mkDTExprs lhs)
                                                     |>.push (AssocList.nil.cons [0,1] .wasChanged |>.cons [1] .willChange, [], [1]  , ← mkDTExprs rhs) }
    | .app (.app _ lhs) rhs =>
      if ← withNewMCtxDepth $ withReducible $ isDefEq (← inferType lhs) (← inferType rhs) then
        result := { result with rewrite_ord     := result.rewrite_ord.push     (AssocList.nil.cons [0,1] .wasChanged |>.cons [1] .willChange, [], [], ← mkDTExprs rhs)
                                rewrite_ord_rev := result.rewrite_ord_rev.push (AssocList.nil.cons [0,1] .willChange |>.cons [1] .wasChanged, [], [], ← mkDTExprs lhs) }
    | _ => pure ()

    result := { result with apply := result.apply.push (AssocList.nil.cons [] .willChange, [], [], ← mkDTExprs e) }
    return result

where
  addBinderKind (diffPos : List Nat) (kind : ℕ) : ProcessResult → ProcessResult :=
    let f := fun (diffs, pos, x) => (diffs.mapKey (diffPos ++ ·), kind :: pos, x)
    fun ⟨a, b, c, d, e⟩ => ⟨a.map f, b.map f, c.map f, d.map f, e.map f⟩


def isSpecific : DTExpr → Bool
  | .star _
  | .const ``Eq #[.star _, .star _, .star _] => false
  | _ => true


def isBadDecl (name : Name) (cinfo : ConstantInfo) (env : Environment) : Bool :=
  (match cinfo with
    | .axiomInfo v => v.isUnsafe
    | .thmInfo .. => false
    | _ => true)
  || (match name with
    | .str _ "inj"
    | .str _ "sizeOf_spec"
    | .str _ "noConfusionType" => true
    | _ => false)
  || name.isInternal'
  || isAuxRecursor env name
  || isNoConfusion env name
  || isMatcherCore env name


def processLemma (name : Name) (cinfo : ConstantInfo) (ds : DiscrTrees) : MetaM DiscrTrees := do
  if isBadDecl name cinfo (← getEnv) then
    return ds

  let ⟨a, b, c, d, e⟩ ← processTree name cinfo.type
  let ⟨a',b',c',d',e'⟩ := ds
  let f := Array.foldl (fun ds (diffs, treePos, pos, es) => es.foldl (init := ds) (fun ds e =>
    if isSpecific e
    then
      ds.insertDTExpr e { name, treePos, pos, diffs := diffs.mapKey (SubExpr.Pos.ofArray ·.toArray)}
    else ds))
  return ⟨f a' a, f b' b, f c' c, f d' d, f e' e⟩

open Std.Tactic

@[reducible] def DiscrTreesCache : Type :=
  DeclCache (DiscrTrees × DiscrTrees)


def DiscrTreesCache.mk (profilingName : String)
    (init : Option DiscrTrees := none) :
    IO DiscrTreesCache :=
  let updateTree := processLemma
  let addDecl := fun name constInfo (tree₁, tree₂) => do
    return (← updateTree name constInfo tree₁, tree₂)
  let addLibraryDecl := fun name constInfo (tree₁, tree₂) => do
    return (tree₁, ← updateTree name constInfo tree₂)
  let s := fun A => A.map (fun lem => (lem.name.toString.length, lem)) |>.qsort (fun p q => p.1 < q.1) |>.map (·.2)
  let post := fun (T₁, ⟨a, b, c, d, e⟩) => return (T₁, ⟨a.mapArrays s, b.mapArrays s,c.mapArrays s, d.mapArrays s, e.mapArrays s⟩)
  match init with
  | some t => return ⟨← Cache.mk (pure ({}, t)), addDecl, addLibraryDecl⟩
  | none => DeclCache.mk profilingName (pre := failure) ({}, {}) addDecl addLibraryDecl (post := post)


def buildDiscrTrees : IO (DiscrTreesCache) := DiscrTreesCache.mk "library search: init cache"

def cachePath : IO System.FilePath := do
  try
    return (← findOLean `LibrarySearch.DiscrTreesData).withExtension "extra"
  catch _ =>
    return "build" / "lib" / "LibrarySearch" / "DiscrTreesData.extra"

initialize cachedData : DiscrTreesCache ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle DiscrTrees path
    -- We can drop the `CompactedRegion` value; we do not plan to free it
    DiscrTreesCache.mk "library search: using cache" (init := some d)
  else
    buildDiscrTrees

def getLibraryLemmas : MetaM (DiscrTrees × DiscrTrees) := cachedData.get




-- open Lean Meta

-- def countingHeartbeats  (x : MetaM α) : MetaM ℕ := do
--   let numHeartbeats ← IO.getNumHeartbeats
--   _ ← x
--   return ((← IO.getNumHeartbeats) - numHeartbeats) / 1000
-- set_option profiler true
-- elab "hiii" : tactic => do
--   -- let x ← mkFreshExprMVar none
--   -- let y := (.lam `_  (.const `Nat []) (.app x $ x) .default)
--   -- logInfo m! "{← mkDTExprs y}, {makeInsertionPath.starEtaExpanded y 0}"
--   let addLibraryDecl : Name → ConstantInfo → DiscrTrees × DiscrTrees → MetaM (DiscrTrees × DiscrTrees) :=
--     fun name constInfo (tree₁, tree₂) => do
--       return (tree₁, ← processLemma name constInfo tree₂)

--   let x ← (countingHeartbeats $ do (← getEnv).constants.map₁.foldM (init := ({}, {})) fun a n c => addLibraryDecl n c a)
--   logInfo m! "{x}"
-- set_option maxHeartbeats 1000000 in
-- example : True := by
--   hiii
--   trivial

-- set_option pp.explicit true
-- set_option pp.explicit false


-- #check MeasureTheory.withDensitySMulLI_apply
-- #check CategoryTheory.HomOrthogonal.matrixDecompositionLinearEquiv_symm_apply
