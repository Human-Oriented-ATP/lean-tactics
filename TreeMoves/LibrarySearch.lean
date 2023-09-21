import TreeRewrite
import TreeRewriteOrd
import Mathlib.Lean.Meta.DiscrTree

namespace Tree

open Lean Meta


inductive LibraryLemmaKind where
| apply
| apply_rev
| rewrite
| rewrite_ord
| rewrite_ord_rev
deriving BEq

structure LibraryLemma where
  name : Name
  tree : Expr
  path : List TreeBinderKind
  specificity : Nat
deriving BEq

structure RewriteLemma extends LibraryLemma where
  isRev : Bool
deriving BEq

structure DiscrTrees where
  apply           : DiscrTree LibraryLemma true := {}
  apply_rev       : DiscrTree LibraryLemma true := {}
  rewrite         : DiscrTree RewriteLemma true := {}
  rewrite_ord     : DiscrTree LibraryLemma true := {}
  rewrite_ord_rev : DiscrTree LibraryLemma true := {}

instance : Inhabited DiscrTrees := ⟨{}⟩ 


private abbrev ProcessResult := Array (Array (DiscrTree.Key true) × LibraryLemma) × Array (Array (DiscrTree.Key true) × LibraryLemma) × Array (Array (DiscrTree.Key true) × RewriteLemma) × Array (Array (DiscrTree.Key true) × LibraryLemma) × Array (Array (DiscrTree.Key true) × LibraryLemma)

-- might want to add some whnf applications with reducible transparency.

partial def processTree (name : Name) : Expr → MetaM ProcessResult
  | .forallE n domain body bi => do
    let mvar ← mkFreshExprMVar domain
    let result ← processTree name (body.instantiate1 mvar)

    let u ← getLevel domain
    if bi.isInstImplicit
    then
      return addBinderKind .inst (fun b => mkApp2 (.const ``Instance [u]) domain (.lam n domain (b.abstract #[mvar]) .default)) result
    else
      if ← pure !body.hasLooseBVars <&&> isLevelDefEq u .zero 
      then
        let result := addBinderKind .imp_right (fun b => mkApp2 (.const ``Imp [u]) domain (.lam n domain b .default)) result
        let key ← DiscrTree.mkPath domain
        return (fun (a,b,c) => (a,b.push (key, {name, tree := domain, path := [], specificity := key.size}),c)) result
      else
        return addBinderKind .all (fun b => mkApp2 (.const ``Forall [u]) domain (.lam n domain (b.abstract #[mvar]) .default)) result

  | regular_exists_pattern n u d body _ =>
    withLocalDeclD n d fun fvar =>
    addBinderKind .ex (fun b => mkApp2 (.const ``Exists [u]) d (.lam n d (b.abstract #[fvar]) .default))
     <$> processTree name (body.instantiate1 fvar)

  | regular_and_pattern p q =>
    pure (fun ⟨a,b,c,d,e⟩ ⟨a',b',c',d',e'⟩ => ⟨a++a',b++b',c++c',d++d',e++e'⟩) <*> addBinderKind .and_left (mkApp2 (.const ``And []) · q) <$> processTree name p
      <*> addBinderKind .and_right (mkApp2 (.const ``And []) p ·) <$> processTree name q
  
  | e => do
    let mut result : ProcessResult := (#[],#[],#[],#[],#[])
    match e with
    | .app (.app (.app (.const ``Eq _) _) lhs) rhs
    | .app (.app (.const ``Iff _) lhs) rhs => do
      let lhsKey ← DiscrTree.mkPath lhs
      let rhsKey ← DiscrTree.mkPath rhs
      result := (fun (a,b,c,d) => (a,b,c.push (lhsKey, {name, tree := e, path := [], specificity := lhsKey.size, isRev := false : RewriteLemma}),d)) result
      result := (fun (a,b,c,d) => (a,b,c.push (rhsKey, {name, tree := e, path := [], specificity := rhsKey.size, isRev := true : RewriteLemma}),d)) result
    | regular_or_pattern .. => pure ()
    | .app (.app _ lhs) rhs =>
      if ← withNewMCtxDepth $ withReducible $ isDefEq (← inferType lhs) (← inferType rhs) then
        let lhsKey ← DiscrTree.mkPath lhs
        let rhsKey ← DiscrTree.mkPath rhs
        result := (fun (a,b,c,d,f) => (a,b,c,d.push (lhsKey, {name, tree := e, path := [], specificity := lhsKey.size}),f)) result
        result := (fun (a,b,c,d,f) => (a,b,c,d,f.push (rhsKey, {name, tree := e, path := [], specificity := rhsKey.size}))) result
    | _ => pure ()

    let key ← DiscrTree.mkPath e
    result := (fun (a,b) => (a.push (key, {name, tree := e, path := [], specificity := key.size}),b)) result
    return result
    
where
  addBinderKind (kind : TreeBinderKind) (mkBinder : Expr → Expr) : ProcessResult → ProcessResult :=
    let f₁ := Bifunctor.snd fun lem => {lem with path := kind :: lem.path, tree := mkBinder lem.tree}
    let f₂ := Bifunctor.snd fun lem => {lem with path := kind :: lem.path, tree := mkBinder lem.tree}
    fun (a,b,c,d,e) => (a.map f₁, b.map f₁, c.map f₂, d.map f₁, e.map f₁)



def processLemma (name : Name) (constInfo : ConstantInfo) (t : DiscrTrees) : MetaM DiscrTrees := do
  if constInfo.isUnsafe then return {}
  if ← name.isBlackListed then return {}

  let (a,b,c,d,e) ← processTree name constInfo.type
  let ⟨a',b',c',d',e'⟩ := t
  let f₁ := Array.foldl (fun t (k, v) => t.insertIfSpecific k v)
  let f₂ := Array.foldl (fun t (k, v) => t.insertIfSpecific k v)
  return ⟨f₁ a' a, f₁ b' b, f₂ c' c, f₁ d' d, f₁ e' e⟩


open Mathlib.Tactic

/--
A type synonym for a `DeclCache` containing a pair of discrimination trees.
The first will store declarations in the current file,
the second will store declarations from imports (and will hopefully be "read-only" after creation).
-/
@[reducible] def DiscrTreesCache : Type :=
  DeclCache (DiscrTrees × DiscrTrees)


/--
Build a `DiscrTreeCache`,
from a function that returns a collection of keys and values for each declaration.
-/
def DiscrTreesCache.mk (profilingName : String)
    (init : Option DiscrTrees := none) :
    IO DiscrTreesCache :=
  let updateTree := fun name constInfo tree => do
    if constInfo.isUnsafe then return {}
    if ← name.isBlackListed then return {}

    let (a,b,c,d,e) ← processTree name constInfo.type
    let ⟨a',b',c',d',e'⟩ := tree
    let f₁ := Array.foldl (fun t (k, v) => t.insertIfSpecific k v)
    let f₂ := Array.foldl (fun t (k, v) => t.insertIfSpecific k v)
    return ⟨f₁ a' a, f₁ b' b, f₂ c' c, f₁ d' d, f₁ e' e⟩

  let addDecl := fun name constInfo (tree₁, tree₂) => do
    return (← updateTree name constInfo tree₁, tree₂)
  let addLibraryDecl := fun name constInfo (tree₁, tree₂) => do
    return (tree₁, ← updateTree name constInfo tree₂)
  let s₁ := fun A => A.map (fun lem => (lem.name.toString.length, lem)) |>.qsort (fun p q => p.1 > q.1) |>.map (·.2)
  let s₂ := fun A => A.map (fun lem => (lem.name.toString.length, lem)) |>.qsort (fun p q => p.1 > q.1) |>.map (·.2)
  let post := fun (T₁, ⟨a,b,c,d,e⟩) => return (T₁, ⟨a.mapArrays s₁, b.mapArrays s₁,c.mapArrays s₂, d.mapArrays s₁, e.mapArrays s₁⟩)
  match init with
  | some t => return ⟨← Cache.mk (pure ({}, t)), addDecl, addLibraryDecl⟩
  | none => DeclCache.mk profilingName ({}, {}) addDecl addLibraryDecl (post := post)


def buildDiscrTrees : IO (DiscrTreesCache) := DiscrTreesCache.mk "library search: init cache"


initialize cachedData : DiscrTreesCache ← unsafe do
  buildDiscrTrees


