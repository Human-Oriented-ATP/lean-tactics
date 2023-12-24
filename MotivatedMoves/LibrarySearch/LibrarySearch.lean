import MotivatedMoves.LibrarySearch.DiscrTree
import Mathlib
import MotivatedMoves.LibrarySearch.Untitled
import MotivatedMoves.LibrarySearch.Untitled2
open Lean Meta
section RefinedDiscrTree
namespace Tree

open RefinedDiscrTree

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

    if bi.isInstImplicit then
      return addBinderKind [1] 1 result
    else
      -- let u ← getLevel domain
      -- if ← pure !body.hasLooseBVars <&&> isLevelDefEq u .zero
      -- then
      --   let result := addBinderKind [1] 1 result
      --   return { result with apply_rev := result.apply_rev.push (AssocList.nil.cons [0] .willChange |>.cons [1] .wasChanged, [0], [], ← mkDTExprs domain) }
      -- else
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
    -- | .app (.app _ lhs) rhs =>
    --   if ← withNewMCtxDepth $ withReducible $ isDefEq (← inferType lhs) (← inferType rhs) then
    --     result := { result with rewrite_ord     := result.rewrite_ord.push     (AssocList.nil.cons [0,1] .wasChanged |>.cons [1] .willChange, [], [], ← mkDTExprs rhs)
    --                             rewrite_ord_rev := result.rewrite_ord_rev.push (AssocList.nil.cons [0,1] .willChange |>.cons [1] .wasChanged, [], [], ← mkDTExprs lhs) }
    | _ => pure ()

    -- result := { result with apply := result.apply.push (AssocList.nil.cons [] .willChange, [], [], ← mkDTExprs e) }
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
  -- let ⟨a',b',c',d',e'⟩ := ds
  -- let f := Array.foldl (fun ds (diffs, treePos, pos, es) => es.foldl (init := ds) (fun ds e =>
  --   if isSpecific e
  --   then
  --     ds.insertDTExpr e { name, treePos, pos, diffs := diffs.mapKey (SubExpr.Pos.ofArray ·.toArray)}
  --   else ds))
  -- return ⟨f a' a, f b' b, f c' c, f d' d, f e' e⟩
  return {}

open Mathlib.Tactic

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
  | none => DeclCache.mk profilingName ({}, {}) addDecl addLibraryDecl (post := post)


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

def countingHeartbeats  (x : MetaM α) : MetaM ℕ := do
  let numHeartbeats ← IO.getNumHeartbeats
  _ ← x
  return ((← IO.getNumHeartbeats) - numHeartbeats) / 1000
elab "hiii" : tactic => do
  -- let x ← mkFreshExprMVar none
  -- let y := (.lam `_  (.const `Nat []) (.app x $ x) .default)
  -- logInfo m! "{← mkDTExprs y}, {makeInsertionPath.starEtaExpanded y 0}"
  let addLibraryDecl : Name → ConstantInfo → DiscrTrees × DiscrTrees → MetaM (DiscrTrees × DiscrTrees) :=
    fun name constInfo (tree₁, tree₂) => do
      return (tree₁, ← processLemma name constInfo tree₂)

  let x ← (countingHeartbeats $ do (← getEnv).constants.map₁.foldM (init := ({}, {})) fun a n c => addLibraryDecl n c a)
  logInfo m! "{x}"


set_option maxHeartbeats 1000000
set_option profiler true

example : True := by
  hiii
  trivial

end Tree
end RefinedDiscrTree



-- namespace Lean.Meta.MyDiscrTree
-- open Mathlib Tactic

-- variable {m : Type → Type} [Monad m]

-- /-- Apply a monadic function to the array of values at each node in a `MyDiscrTree`. -/
-- partial def Trie.mapArraysM (t : MyDiscrTree.Trie α) (f : Array α → m (Array β)) :
--     m (MyDiscrTree.Trie β) :=
--   match t with
--   | .node vs children =>
--     return .node (← f vs) (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))

-- /-- Apply a monadic function to the array of values at each node in a `MyDiscrTree`. -/
-- def mapArraysM (d : MyDiscrTree α) (f : Array α → m (Array β)) : m (MyDiscrTree β) := do
--   pure { root := ← d.root.mapM (fun t => t.mapArraysM f) }

-- /-- Apply a function to the array of values at each node in a `MyDiscrTree`. -/
-- def mapArrays (d : MyDiscrTree α) (f : Array α → Array β) : MyDiscrTree β :=
--   Id.run <| d.mapArraysM fun A => pure (f A)

-- def insertIfSpecific [BEq α] (d : MyDiscrTree α)
--     (keys : Array MyDiscrTree.Key) (v : α) (config : WhnfCoreConfig) : MyDiscrTree α :=
--   if keys == #[MyDiscrTree.Key.star] || keys == #[MyDiscrTree.Key.const `Eq 3, Key.star, Key.star, Key.star] then
--     d
--   else
--     d.insertCore keys v config

-- def DiscrTreeCache.mk [BEq α] (profilingName : String)
--     (processDecl : Name → ConstantInfo → MetaM (Array (Array MyDiscrTree.Key × α))) :
--     MetaM (MyDiscrTree α) := do
--   let updateTree : Name → ConstantInfo → MyDiscrTree α → MetaM (MyDiscrTree α) := fun name constInfo tree => do
--     return (← processDecl name constInfo).foldl (init := tree) fun t (k, v) =>
--       insertIfSpecific t k v {}
--   let addLibraryDecl := fun name constInfo tree =>
--     updateTree name constInfo tree
--   (← getEnv).constants.map₁.foldM (init := {}) fun a n c =>
--         addLibraryDecl n c a

-- /-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting forwards. -/
-- def forwardWeight := 2
-- /-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting backwards. -/
-- def backwardWeight := 1

-- /-- Configuration for `DiscrTree`. -/
-- def discrTreeConfig : WhnfCoreConfig := {}

-- /-- Prepare the discrimination tree entries for a lemma. -/
-- def processLemma (name : Name) (constInfo : ConstantInfo) :
--     MetaM (Array (Array MyDiscrTree.Key × (Name × Bool × Nat))) := do
--   if constInfo.isUnsafe then return #[]
--   if ← name.isBlackListed then return #[]
--   -- We now remove some injectivity lemmas which are not useful to rewrite by.
--   if name matches .str _ "injEq" then return #[]
--   if name matches .str _ "sizeOf_spec" then return #[]
--   match name with
--   | .str _ n => if n.endsWith "_inj" ∨ n.endsWith "_inj'" then return #[]
--   | _ => pure ()
--   withNewMCtxDepth do withReducible do
--     let (_, _, type) ← forallMetaTelescopeReducing constInfo.type
--     match type.getAppFnArgs with
--     | (``Eq, #[_, lhs, rhs])
--     | (``Iff, #[lhs, rhs]) => do
--       let lhsKey ← MyDiscrTree.mkPath lhs {}
--       let rhsKey ← MyDiscrTree.mkPath rhs {}
--       return #[(lhsKey, (name, false, forwardWeight * lhsKey.size)),
--         (rhsKey, (name, true, backwardWeight * rhsKey.size))]
--     | _ => return #[]

-- /-- Construct the discrimination tree of all lemmas. -/
-- def buildDiscrTree : MetaM (MyDiscrTree (Name × Bool × Nat)) := do
--   DiscrTreeCache.mk "rw?: init cache" processLemma
--     -- Sort so lemmas with longest names come first.
--     -- This is counter-intuitive, but the way that `DiscrTree.getMatch` returns results
--     -- means that the results come in "batches", with more specific matches *later*.
--     -- Thus we're going to call reverse on the result of `DiscrTree.getMatch`,
--     -- so if we want to try lemmas with shorter names first,
--     -- we need to put them into the `DiscrTree` backwards.


-- #check isExprDefEqAuxImpl

-- #check Fin2
-- def f := show MetaM _ from do
--   let x ← Tree.countingHeartbeats (do
--     let y ← buildDiscrTree
--     return (y).root.size == 0)
--   return x

-- set_option profiler true
-- set_option maxHeartbeats 1000000

-- #eval f


-- #check inferTypeImp
#check MLList2.uncons?
