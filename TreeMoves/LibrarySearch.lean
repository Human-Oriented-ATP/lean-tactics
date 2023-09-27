import TreeMoves.DiscrTree
namespace Tree

open DiscrTree Lean Meta

inductive LibraryLemmaKind where
| apply
| apply_rev
| rewrite
| rewrite_ord
| rewrite_ord_rev
deriving BEq

structure LibraryLemma where
  name : Name
  path : List TreeBinderKind
  pos : List Nat
  diffs : AssocList SubExpr.Pos Widget.DiffTag

instance : BEq LibraryLemma where
  beq := fun {name, path, pos, ..} {name := name', path := path', pos := pos', ..} => name == name' && pos == pos' && path == path'
instance : ToFormat LibraryLemma where
  format := (toString ·.name)



structure DiscrTrees where
  apply           : DiscrTree LibraryLemma true := {}
  apply_rev       : DiscrTree LibraryLemma true := {}
  rewrite         : DiscrTree LibraryLemma true := {}
  rewrite_ord     : DiscrTree LibraryLemma true := {}
  rewrite_ord_rev : DiscrTree LibraryLemma true := {}

instance : Inhabited DiscrTrees := ⟨{}⟩ 

-- private abbrev Quintuple α := α × α × α × α × α
-- private abbrev ProcessResult := Quintuple (Array (AssocList (List Nat) Widget.DiffTag × List TreeBinderKind × List Nat × Array (DiscrTree.Key true)))

private structure ProcessResult where
  apply           : Array (AssocList (List Nat) Widget.DiffTag × List TreeBinderKind × List Nat × Array DiscrTree.Key) := #[]
  apply_rev       : Array (AssocList (List Nat) Widget.DiffTag × List TreeBinderKind × List Nat × Array DiscrTree.Key) := #[]
  rewrite         : Array (AssocList (List Nat) Widget.DiffTag × List TreeBinderKind × List Nat × Array DiscrTree.Key) := #[]
  rewrite_ord     : Array (AssocList (List Nat) Widget.DiffTag × List TreeBinderKind × List Nat × Array DiscrTree.Key) := #[]
  rewrite_ord_rev : Array (AssocList (List Nat) Widget.DiffTag × List TreeBinderKind × List Nat × Array DiscrTree.Key) := #[]
instance : Append ProcessResult where
  append := (fun ⟨a, b, c, d, e⟩ ⟨a',b',c',d',e'⟩ => ⟨a++a',b++b',c++c',d++d',e++e'⟩)

-- might want to add some whnf applications with reducible transparency?
partial def processTree : Expr → MetaM ProcessResult
  | .forallE n domain body bi => do
    let mvar ← mkFreshExprMVar domain (userName := n)
    let result ← processTree (body.instantiate1 mvar)

    let u ← getLevel domain
    if bi.isInstImplicit
    then
      return addBinderKind [1] .inst result
    else
      if ← pure !body.hasLooseBVars <&&> isLevelDefEq u .zero 
      then
        let result := addBinderKind [1] .imp_right result
        return { result with apply_rev := result.apply_rev.push (AssocList.nil.cons [0] .willChange |>.cons [1] .wasChanged, [.imp_left], [], ← mkPath domain) }
      else
        return addBinderKind [1] .all result

  | regular_exists_pattern n _u d body _ =>
    withLocalDeclD n d fun fvar =>
    addBinderKind [1,1] .ex <$> processTree (body.instantiate1 fvar)

  | regular_and_pattern p q =>
    return (← addBinderKind [0,1] .and_left <$> processTree p) ++ (← addBinderKind [1] .and_right <$> processTree q)
  
  | e => do
    let mut result : ProcessResult := {}
    match e with
    | .app (.app (.app (.const ``Eq _) _) lhs) rhs
    | .app (.app (.const ``Iff _) lhs) rhs => do
      result := { result with rewrite := result.rewrite.push (AssocList.nil.cons [0,1] .willChange |>.cons [1] .wasChanged, [], [0,1], ← mkPath lhs)
                                                     |>.push (AssocList.nil.cons [0,1] .wasChanged |>.cons [1] .willChange, [], [1]  , ← mkPath rhs) }
    | .app (.app _ lhs) rhs =>
      if ← withNewMCtxDepth $ withReducible $ isDefEq (← inferType lhs) (← inferType rhs) then
        result := { result with rewrite_ord     := result.rewrite_ord.push     (AssocList.nil.cons [0,1] .wasChanged |>.cons [1] .willChange, [], [], ← mkPath rhs)
                                rewrite_ord_rev := result.rewrite_ord_rev.push (AssocList.nil.cons [0,1] .willChange |>.cons [1] .wasChanged, [], [], ← mkPath lhs) }
    | _ => pure ()

    result := { result with apply := result.apply.push (AssocList.nil.cons [] .willChange, [], [], ← mkPath e) }
    return result
    
where
  addBinderKind (pos : List Nat) (kind : TreeBinderKind) : ProcessResult → ProcessResult :=
    let f := fun (diffs, path, x) => (diffs.mapKey (pos ++ ·), kind :: path, x)
    fun ⟨a, b, c, d, e⟩ => ⟨a.map f, b.map f, c.map f, d.map f, e.map f⟩


def processLemma (name : Name) (cinfo : ConstantInfo) (t : DiscrTrees) : MetaM DiscrTrees := do
  if cinfo.isUnsafe then return t
  if ← name.isBlackListed then return t
  if name matches .str _ "sizeOf_spec" then return t
  unless ← (match cinfo with
    | .axiomInfo ..
    | .thmInfo .. => pure true
    -- | .defnInfo .. => do
    --   let us ← mkFreshLevelMVarsFor cinfo
    --   isDefEq (← inferType (← instantiateTypeLevelParams cinfo us)) (.sort .zero)
    | _ => pure false)
    do return t
  let ⟨a, b, c, d, e⟩ ← processTree cinfo.type
  let ⟨a',b',c',d',e'⟩ := t
  let f := Array.foldl (fun t (diffs, path, pos, key) => t.insertCore key { name, path, pos, diffs := diffs.mapKey (SubExpr.Pos.ofArray ·.toArray)})
  return ⟨f a' a, f b' b, f c' c, f d' d, f e' e⟩

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


initialize cachedData : DiscrTreesCache ← unsafe do
  buildDiscrTrees

def getLibraryLemmas : MetaM (DiscrTrees × DiscrTrees) := cachedData.cache.get
