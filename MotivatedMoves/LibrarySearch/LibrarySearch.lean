import MotivatedMoves.LibrarySearch.DiscrTree
import Mathlib
namespace MotivatedTree

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

def LibraryLemma.length (lem : LibraryLemma) : Nat :=
  lem.name.toString.length

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
partial def processTree : Expr → MetaM ProcessResult
  | .forallE n domain body bi => do
    let mvar ← mkFreshExprMVar domain (userName := n)
    let result ← processTree (body.instantiate1 mvar)
    let result := addBinderKind [1] 1 result
    -- if bi.isExplicit && !body.hasLooseBVars then
    --   if ← isProp domain then
    --     return { result with apply_rev := result.apply_rev.push (AssocList.nil.cons [0] .willChange |>.cons [1] .wasChanged, [0], [], ← mkDTExprs domain {}) }
    return result

  | regular_exists_pattern n _u d body _ =>
    withLocalDeclD n d fun fvar =>
    addBinderKind [1,1] 1 <$> processTree (body.instantiate1 fvar)

  | regular_and_pattern p q =>
    return (← addBinderKind [0,1] 0 <$> processTree p) ++ (← addBinderKind [1] 1 <$> processTree q)

  | e => do
    let mut result : ProcessResult := {}
    match e with
    -- | .app (.app (.app (.const ``Eq _) _) lhs) rhs
    -- | .app (.app (.const ``Iff _) lhs) rhs =>
    --   result := { result with rewrite := result.rewrite.push (AssocList.nil.cons [0,1] .willChange |>.cons [1] .wasChanged, [], [0,1], ← mkDTExprs lhs {})
                                                    --  |>.push (AssocList.nil.cons [0,1] .wasChanged |>.cons [1] .willChange, [], [1]  , ← mkDTExprs rhs {}) }
    -- | .app (.app _ lhs) rhs =>
    --   if ← withNewMCtxDepth $ withReducible $ isDefEq (← inferType lhs) (← inferType rhs) then
    --     result := { result with rewrite_ord     := result.rewrite_ord.push     (AssocList.nil.cons [0,1] .wasChanged |>.cons [1] .willChange, [], [], ← mkDTExprs rhs {})
    --                             rewrite_ord_rev := result.rewrite_ord_rev.push (AssocList.nil.cons [0,1] .willChange |>.cons [1] .wasChanged, [], [], ← mkDTExprs lhs {}) }
    | _ => pure ()

    result := { result with apply := result.apply.push (AssocList.nil.cons [] .willChange, [], [], ← mkDTExprs e {}) }
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
    | .str _ "injEq"
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

  let ⟨a, b, c, d, e⟩ ← processTree cinfo.type
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
  DeclCache.mk profilingName (pre := pre) ({}, {}) addDecl addLibraryDecl (post := post)
where
  pre := do
    let .some libraryTrees := init | failure
    return ({}, libraryTrees)
  updateTree := processLemma
  addDecl := fun name constInfo (tree₁, tree₂) => do
    return (← updateTree name constInfo tree₁, tree₂)
  addLibraryDecl := fun name constInfo (tree₁, tree₂) => do
    return (tree₁, ← updateTree name constInfo tree₂)
  sort := Array.qsort (lt := (·.length < ·.length))
  post := fun (T₁, ⟨a, b, c, d, e⟩) => return (T₁, ⟨a.mapArrays sort, b.mapArrays sort,c.mapArrays sort, d.mapArrays sort, e.mapArrays sort⟩)

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
    DiscrTreesCache.mk "library search: init cache"

def getLibraryLemmas : MetaM (DiscrTrees × DiscrTrees) := cachedData.get




def countingHeartbeats  (x : MetaM α) : MetaM ℕ := do
  let numHeartbeats ← IO.getNumHeartbeats
  _ ← x
  return ((← IO.getNumHeartbeats) - numHeartbeats) / 1000
elab "hiii" : tactic => do
  let addLibraryDecl : Name → ConstantInfo → DiscrTrees × DiscrTrees → MetaM (DiscrTrees × DiscrTrees) :=
    fun name constInfo (tree₁, tree₂) => do
      return (tree₁, ← processLemma name constInfo tree₂)
  -- let n := ``HasDerivAt.add
  let x ← ( countingHeartbeats do
      (← getEnv).constants.map₁.foldM (init := ({}, {})) fun a n c => do
        try
          addLibraryDecl n c a
        catch err =>
          logInfo m! "{n}, {err.toMessageData}"
          return a)
  logInfo m! "{x}"
set_option maxHeartbeats 1000000
set_option profiler true
-- set_option trace.Meta.isDefEq true in
-- set_option pp.explicit true in
example : True := by
  hiii
  trivial



-- #check CategoryTheory.Mat
-- #check CategoryTheory.Mat_
-- #check ENNReal.iInf_add_iInf
-- #eval 755067 - 754989
#check 456408 - 89.8
#check 444365 - 75.6
#check 446662 - 85.8
#check Set.preimage_const_add_Ioi
#check HasStrictFDerivAt.clm_comp
#check 436997 - 89 - 79.1
#check 435996 - 77.2
#check 440887 - 75.3
#check - 73.3

#check 438243


#check ProbabilityTheory.kernel.integral_integral_add'
#check MeasureTheory.integral_integral_add'
#check MeasureTheory.integral_exp_tilted
#check volume_regionBetween_eq_lintegral
#check Continuous.mul
#check Matrix.updateRow_eq_transvection
#check CategoryTheory.Mat.add_apply
#check Pi.add_apply
#check DMatrix.add_apply
#check FormalMultilinearSeries.neg_apply
#check tendsto_inv_atTop_zero
#check ContinuousAt.inv₀
