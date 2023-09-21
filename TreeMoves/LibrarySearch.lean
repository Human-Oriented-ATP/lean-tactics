import Tree
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
  path : List TreeBinderKind
  pos : List Nat
deriving BEq

def LibraryLemma.proofAndType (lem : LibraryLemma) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo lem.name
  let us ← mkFreshLevelMVarsFor cinfo
  return (.const lem.name us, ← instantiateTypeLevelParams cinfo us)



structure DiscrTrees where
  apply           : DiscrTree LibraryLemma true := {}
  apply_rev       : DiscrTree LibraryLemma true := {}
  rewrite         : DiscrTree LibraryLemma true := {}
  rewrite_ord     : DiscrTree LibraryLemma true := {}
  rewrite_ord_rev : DiscrTree LibraryLemma true := {}

instance : Inhabited DiscrTrees := ⟨{}⟩ 


private abbrev ProcessResult := Array (Array (DiscrTree.Key true) × LibraryLemma) × Array (Array (DiscrTree.Key true) × LibraryLemma) × Array (Array (DiscrTree.Key true) × LibraryLemma) × Array (Array (DiscrTree.Key true) × LibraryLemma) × Array (Array (DiscrTree.Key true) × LibraryLemma)

-- might want to add some whnf applications with reducible transparency.
partial def processTree (name : Name) : Expr → MetaM ProcessResult
  | .forallE n domain body bi => do
    let mvar ← mkFreshExprMVar domain (userName := n)
    let result ← processTree name (body.instantiate1 mvar)

    let u ← getLevel domain
    if bi.isInstImplicit
    then
      return addBinderKind .inst result
    else
      if ← pure !body.hasLooseBVars <&&> isLevelDefEq u .zero 
      then
        let result := addBinderKind .imp_right result
        let key ← DiscrTree.mkPath domain
        return (fun (a,b,c) => (a,b.push (key, {name, path := [.imp_left], pos := []}),c)) result
      else
        return addBinderKind .all result

  | regular_exists_pattern n _u d body _ =>
    withLocalDeclD n d fun fvar =>
    addBinderKind .ex <$> processTree name (body.instantiate1 fvar)

  | regular_and_pattern p q =>
    pure (fun ⟨a, b, c, d, e⟩ ⟨a',b',c',d',e'⟩ => ⟨a++a',b++b',c++c',d++d',e++e'⟩) <*> addBinderKind .and_left <$> processTree name p
      <*> addBinderKind .and_right<$> processTree name q
  
  | e => do
    let mut result : ProcessResult := (#[],#[],#[],#[],#[])
    match e with
    | .app (.app (.app (.const ``Eq _) _) lhs) rhs
    | .app (.app (.const ``Iff _) lhs) rhs => do
      let lhsKey ← DiscrTree.mkPath lhs
      let rhsKey ← DiscrTree.mkPath rhs
      result := (fun (a,b,c,d) => (a,b,c.push (lhsKey, {name, path := [], pos := [0,1]}),d)) result
      result := (fun (a,b,c,d) => (a,b,c.push (rhsKey, {name, path := [], pos := [1]}),d)) result
    | .app (.app _ lhs) rhs =>
      if ← withNewMCtxDepth $ withReducible $ isDefEq (← inferType lhs) (← inferType rhs) then
        let lhsKey ← DiscrTree.mkPath lhs
        let rhsKey ← DiscrTree.mkPath rhs
        result := (fun (a,b,c,d,f) => (a,b,c,d.push (lhsKey, {name, path := [], pos := []}),f)) result
        result := (fun (a,b,c,d,f) => (a,b,c,d,f.push (rhsKey, {name, path := [], pos := []}))) result
    | _ => pure ()

    let key ← DiscrTree.mkPath e
    result := (fun (a,b) => (a.push (key, {name, path := [],  pos := []}),b)) result
    return result
    
where
  addBinderKind (kind : TreeBinderKind) : ProcessResult → ProcessResult :=
    let f := Bifunctor.snd fun lem => {lem with path := kind :: lem.path}
    fun (a, b, c, d, e) => (a.map f, b.map f, c.map f, d.map f, e.map f)



def processLemma (name : Name) (constInfo : ConstantInfo) (t : DiscrTrees) : MetaM DiscrTrees := do
  if constInfo.isUnsafe then return {}
  if ← name.isBlackListed then return {}

  let (a, b, c, d, e) ← processTree name constInfo.type
  let ⟨a',b',c',d',e'⟩ := t
  let f := Array.foldl (fun t (k, v) => t.insertIfSpecific k v)
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
  let s := fun A => A.map (fun lem => (lem.name.toString.length, lem)) |>.qsort (fun p q => p.1 > q.1) |>.map (·.2)
  let post := fun (T₁, ⟨a, b, c, d, e⟩) => return (T₁, ⟨a.mapArrays s, b.mapArrays s,c.mapArrays s, d.mapArrays s, e.mapArrays s⟩)
  match init with
  | some t => return ⟨← Cache.mk (pure ({}, t)), addDecl, addLibraryDecl⟩
  | none => DeclCache.mk profilingName ({}, {}) addDecl addLibraryDecl (post := post)


def buildDiscrTrees : IO (DiscrTreesCache) := DiscrTreesCache.mk "library search: init cache"


initialize cachedData : DiscrTreesCache ← unsafe do
  buildDiscrTrees

def getLibraryLemmas : MetaM (DiscrTrees × DiscrTrees) := cachedData.cache.get


--------------


-- def libApply (lem : LibraryLemma) (pol : Bool) (tree : Expr) (goalPath : List TreeBinderKind) (goalPos : List Nat) (unification : Unification) : MetaM TreeProof := do
--   let us ← mkFreshLevelMVars lem.lvlParams.length
--   let hyp := lem.tree.instantiateLevelParams lem.lvlParams us
--   let proof := .const lem.name us
--   Monad.join (applyAux proof hyp tree true lem.path goalPath hypPos goalPos unification) |>.run' {}






-----

open DiscrTree


private partial def isNumeral (e : Expr) : Bool :=
  if e.isNatLit then true
  else
    let f := e.getAppFn
    if !f.isConst then false
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then isNumeral e.appArg!
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then isNumeral (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then true
      else false



private partial def toNatLit? (e : Expr) : Option Literal :=
  if isNumeral e then
    if let some n := loop e then
      some (.natVal n)
    else
      none
  else
    none
where
  loop (e : Expr) : OptionT Id Nat := do
    let f := e.getAppFn
    match f with
    | .lit (.natVal n) => return n
    | .const fName .. =>
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then
        let r ← loop e.appArg!
        return r+1
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then
        loop (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then
        return 0
      else
        failure
    | _ => failure

private def elimLooseBVarsByBeta (e : Expr) : CoreM Expr :=
  Core.transform e
    (pre := fun e => do
      if !e.hasLooseBVars then
        return .done e
      else if e.isHeadBetaTarget then
        return .visit e.headBeta
      else
        return .continue)


private def getKeyArgs (e : Expr) (isMatch root : Bool) : MetaM (Key s × Array Expr) := do
  let e ← reduceDT e root (simpleReduce := s)
  unless root do
    if let some v := toNatLit? e then
      return (.lit v, #[])
  match e.getAppFn with
  | .lit v         => return (.lit v, #[])
  | .const c _     =>
    if (← getConfig).isDefEqStuckEx && e.hasExprMVar then
      if (← isReducible c) then
        Meta.throwIsDefEqStuck
      else if let some matcherInfo := isMatcherAppCore? (← getEnv) e then
        let args := e.getAppArgs
        for arg in args[matcherInfo.getFirstDiscrPos: matcherInfo.getFirstDiscrPos + matcherInfo.numDiscrs] do
          if arg.hasExprMVar then
            Meta.throwIsDefEqStuck
      else if (← isRec c) then
        Meta.throwIsDefEqStuck
    let nargs := e.getAppNumArgs
    return (.const c nargs, e.getAppRevArgs)
  | .fvar fvarId   =>
    let nargs := e.getAppNumArgs
    return (.fvar fvarId nargs, e.getAppRevArgs)
  | .mvar mvarId   =>
    if isMatch then
      return (.other, #[])
    else do
      let ctx ← read
      if ctx.config.isDefEqStuckEx then
        return (.star, #[])
      else if (← mvarId.isReadOnlyOrSyntheticOpaque) then
        return (.other, #[])
      else
        return (.star, #[])
  | .proj s i a .. =>
    let nargs := e.getAppNumArgs
    return (.proj s i nargs, #[a] ++ e.getAppRevArgs)
  | .forallE _ d b _ =>
    let b ← if b.hasLooseBVars then elimLooseBVarsByBeta b else pure b
    if b.hasLooseBVars then
      return (.other, #[])
    else
      return (.arrow, #[d, b])
  | _ =>
    return (.other, #[])

private abbrev getMatchKeyArgs (e : Expr) (root : Bool) : MetaM (Key s × Array Expr) :=
  getKeyArgs e (isMatch := true) (root := root)

private abbrev getUnifyKeyArgs (e : Expr) (root : Bool) : MetaM (Key s × Array Expr) :=
  getKeyArgs e (isMatch := false) (root := root)

private def getStarResult (d : DiscrTree α s) : Array (α × Nat) :=
  let result : Array (α × Nat) := .mkEmpty 8
  match d.root.find? .star with
  | none                  => result
  | some (.node vs _) => result ++ vs.map (·, 0)

private abbrev findKey (cs : Array (Key s × Trie α s)) (k : Key s) : Option (Key s × Trie α s) :=
  cs.binSearch (k, default) (fun a b => a.1 < b.1)


partial def getUnifyWithSpecificity (d : DiscrTree α s) (e : Expr) : MetaM (Array (α × Nat)) :=
  withReducible do
    let (k, args) ← getUnifyKeyArgs e (root := true)
    match k with
    | .star => throwError "the unification pattern is a metavariable"--d.root.foldlM (init := #[]) fun result k c => process k.arity 0 #[] c result
    | _ =>
      let result := getStarResult d
      match d.root.find? k with
      | none   => return result
      | some c => process 0 1 args c result
where
  process (skip : Nat) (specific : Nat) (todo : Array Expr) (c : Trie α s) (result : Array (α × Nat)) : MetaM (Array (α × Nat)) := do
    match skip, c with
    | skip+1, .node _  cs =>
      if cs.isEmpty then
        return result
      else
        cs.foldlM (init := result) fun result ⟨k, c⟩ => process (skip + k.arity) specific todo c result
    | 0, .node vs cs => do
      if todo.isEmpty then
        return result ++ vs.map (·, specific)
      else if cs.isEmpty then
        return result
      else
        let e     := todo.back
        let todo  := todo.pop
        let (k, args) ← getUnifyKeyArgs e (root := false)
        let visitStar (result : Array (α × Nat)) : MetaM (Array (α × Nat)) :=
          let first := cs[0]!
          if first.1 == .star then
            process 0 specific todo first.2 result
          else
            return result
        let visitNonStar (k : Key s) (args : Array Expr) (result : Array (α × Nat)) : MetaM (Array (α × Nat)) :=
          match findKey cs k with
          | none   => return result
          | some c => process 0 (specific + 1) (todo ++ args) c.2 result
        match k with
        | .star  => cs.foldlM (init := result) fun result (k, c) => process specific k.arity todo c result
        | .arrow => visitNonStar .other #[] (← visitNonStar k args (← visitStar result))
        | _      => visitNonStar k args (← visitStar result)


structure LibraryMove where
  lemmaName : Name
  lemmaType : String
  tactic : String


-- def libraryApplySearch (e : Expr) (pos : List Nat) : MetaM LibraryMove := do
--   let lems ← getLibraryLemmas
--   let (goalPath, goalPos) := positionToPath pos e
--   let lems := if PathToPolarity goalPath then (lems.1.apply, lems.2.apply) else (lems.1.apply_rev, lems.2.apply_rev)
--   let candidates := (← getUnifyWithSpecificity lems.1 ) ++ (← lems.getUnifyWithSpecificity)

--   sorry
-- def libraryRewriteSearch (e : Expr) (pos : List Nat) : MetaM LibraryMove := do
--   let lems ← getLibraryLemmas
--   let (goalPath, goalPos) := positionToPath pos e
--   let lems := (lems.1.rewrite, lems.2.rewrite)
--   sorry
-- def libraryRewriteOrdSearch (e : Expr) (pos : List Nat) : MetaM LibraryMove := do
--   let lems ← getLibraryLemmas
--   let (goalPath, goalPos) := positionToPath pos e
--   sorry