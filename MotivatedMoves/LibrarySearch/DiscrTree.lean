import MotivatedMoves.LibrarySearch.DiscrTreeTypes
import MotivatedMoves.ProofState.Tree

namespace Tree.DiscrTree

open Lean Meta DiscrTree

/-! 
This file is a modification of DiscrTree.lean in Lean, with some parts removed and some new features added.
I document only what is different from that file.

We define discrimination trees for the purpose of unifying local expressions with library results that apply at that expression.

These are the features that are not in Lean's discrimination trees:

- The constructor `Key.fvar` and `Key.star` now take a `Nat` as an argument, as an identifier.
  For example, the library pattern `a+a` is encoded as `[⟨Hadd.hadd, 6⟩, *0, *0, *0, *1, *2, *2]`.
  `*0` is the type of `a`, `*1` is the `Hadd` instance, and `*2` is `a`.
  This means that it will only match an expression `x+y` if `x` is definitionally equal to `y`.

  `Key.fvar` is used in lemmas like `Nat.exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Prime p ∧ p ∣ n`,
  where the part `Prime p` gets the pattern `[⟨Nat.Prime, 1⟩, .fvar 0 0]`.
  the first argument of `Key.fvar` is the identifier, and the second argument is the arity.

  If a discrimination tree is built locally, there is a need for a `Key.fvar` that takes an `FVarId`
  as an idenitifier, which is what the DiscrTree defined in Lean does, but this is of no use for us.

- The constructors `Key.lam`, `Key.forall` and `Key.bvar` have been introduced in order to allow for patterns under binders.
  For example, this allows for more specific matching with the left hand side of
  `Finset.sum_range_id (n : ℕ) : ∑ i in range n, i = n * (n - 1) / 2`

- We keep track of a matching score of a unification. 
  This score represent the number of keys that had to be the same for the unification to succeed.
  For example, matching `(1 + 2) + 3` with `add_comm` gives a score of 3,
  since the pattern of commutativity is [⟨Hadd.hadd, 6⟩, *0, *0, *0, *1, *2, *3],
  so matching `⟨Hadd.hadd, 6⟩` gives 1 point, 
  and matching `*0` two times after its first appearence gives another 2 points.
  Similarly, matching it with `add_assoc` gives a score of 7.

  TODO: the third type parameter of `Hadd.hadd` is an outparam, so its matching should not be counted to the score.

-/

def Key.ctorIdx : Key → Nat
  | .star ..  => 0
  | .sort     => 1
  | .lit ..   => 2
  | .fvar ..  => 3
  | .bvar ..  => 4
  | .lam      => 5
  | .forall   => 6
  | .proj ..  => 7
  | .const .. => 8

def Key.lt : Key → Key → Bool
  | .star i₁,       .star i₂       => i₁ < i₂
  | .lit v₁,        .lit v₂        => v₁ < v₂
  | .fvar n₁ a₁,    .fvar n₂ a₂    => n₁ < n₂ || (n₁ == n₂ && a₁ < a₂)
  | .const n₁ a₁,   .const n₂ a₂   => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ => Name.quickLt s₁ s₂ || (s₁ == s₂ && i₁ < i₂) || (s₁ == s₂ && i₁ == i₂ && a₁ < a₂)
  | .bvar i₁ a₁,    .bvar i₂ a₂    => i₁ < i₂ || (i₁ == i₂ && a₁ < a₂)
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

def Key.format : Key → Format
  | .star i                 => "*" ++ Std.format i
  | .sort                   => "◾"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .const k a              => "⟨" ++ Std.format k ++ ", " ++ Std.format a ++ "⟩"
  | .proj s i a             => "⟨" ++ Std.format s ++ "." ++ Std.format i ++ ", " ++ Std.format a ++ "⟩"
  | .fvar k a               => "⟨" ++ "f" ++ Std.format k ++ ", " ++ Std.format a ++ "⟩"
  | .bvar i a               => "⟨" ++ "#" ++ Std.format i ++ ", " ++ Std.format a ++ "⟩"
  | .forall                 => "→"
  | .lam                    => "λ"

instance : ToFormat Key := ⟨Key.format⟩

def Key.arity : Key → Nat
  | .const _ a  => a
  | .fvar _ a   => a
  | .bvar _ a   => a
  | .lam        => 1
  | .forall     => 2
  | .proj _ _ a => 1 + a
  | _           => 0

instance : Inhabited (Trie α) := ⟨.node #[]⟩

def empty : DiscrTree α := { root := {} }

partial def Trie.format [ToFormat α] : Trie α → Format
  | .node cs => Format.group $ Format.paren $
    "node" ++ Format.join (cs.toList.map fun (k, c) => Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))
  | .values vs => "values" ++ if vs.isEmpty then Format.nil else " " ++ Std.format vs
  | .path ks c => Std.format ks ++ " => " ++ format c
  

instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩

partial def format [ToFormat α] (d : DiscrTree α) : Format :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × Format) k c =>
      (false, p.2 ++ (if p.1 then Format.nil else Format.line) ++ Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (DiscrTree α) := ⟨format⟩


partial def DTExpr.format : DTExpr → Format
  | .star n                 => "*" ++ n.1.toString
  | .sort                   => "◾"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .const n as             => Std.format n  ++ if as.isEmpty then .nil else Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")
  | .proj _ i a as          => DTExpr.format a ++ "." ++ Std.format i ++ if as.isEmpty then .nil else Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")
  | .fvar n as              => "f" ++ n.1.toString ++ if as.isEmpty then .nil else Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")
  | .bvar i as              => "#" ++ Std.format i  ++ if as.isEmpty then .nil else Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")
  | .forall d b             => DTExpr.format d ++ " → " ++ DTExpr.format b
  | .lam b                  => "λ " ++ DTExpr.format b

instance : ToFormat DTExpr := ⟨DTExpr.format⟩

/-- Checks whether there is any potential η-reduction in `e`.
This is useful for avoiding the more expensive function `getEtas`. -/
partial def hasEta (e : DTExpr) (inLambda : Bool := false) : Bool :=
  match e with
  | .const _ as             => (inLambda && as.back? matches some (.star _)) || as.any hasEta
  | .proj _ _ a as          => (inLambda && as.back? matches some (.star _)) || as.any hasEta || hasEta a
  | .fvar _ as              => (inLambda && as.back? matches some (.star _)) || as.any hasEta
  | .bvar _ as              => (inLambda && as.back? matches some (.star _)) || as.any hasEta
  | .forall d b             => hasEta d || hasEta b
  | .lam b                  => hasEta b (inLambda := true)
  | _                       => false


/-- Given `e : DTExpr` that consists of `n` lambda's and body `b`, returns `f n b`. -/
def _root_.Tree.DTExpr.withLambdas (f : Nat → DTExpr → α) : DTExpr → α :=
  let rec go (i : Nat) : DTExpr → α
    | .lam e => go (i+1) e
    | e => f i e
  go 0

/-- Drops at most `max` stars from the end of `e`, returning the resulting `DTExpr` and the removed stars. -/
private def dropStars (max : Nat) (e : DTExpr) : DTExpr × Array DTExpr :=
  let go (args : Array DTExpr) : Array DTExpr × Array DTExpr := Id.run do
    let mut args := args
    let mut stars := #[]
    for _ in [:max] do
      match args.back? with
      | some star@(.star _) =>
        args := args.pop
        stars := stars.push star
      | _ =>
        break
    return (args, stars.reverse)
  match e with
  | .const n args    => Bifunctor.fst (.const n)    $ go args
  | .fvar i args     => Bifunctor.fst (.fvar i)     $ go args
  | .bvar i args     => Bifunctor.fst (.bvar i)     $ go args
  | .proj n i e args => Bifunctor.fst (.proj n i e) $ go args
  | _ => (e, #[])

/-- Given the body `e` of some η-reduced `DTExpr`, which had `lambdas` and `stars` removed,
returns all possible η equivalent forms. -/
private def reEta (lambdas : Nat) (stars : Array DTExpr) (e : DTExpr) : List DTExpr :=
  let go (args : Array DTExpr) (c : Array DTExpr → DTExpr) : List DTExpr := Id.run do
    let c (i : Nat) (args : Array DTExpr) :=
      i.repeat .lam (c args)
    let mut i := lambdas - stars.size
    let mut args := args
    let mut result := [c i args]
    for star in stars do
      i := i + 1
      args := args.push star
      result := result.cons (c i args)
    return result
  match e with
  | .const n args    => go args (.const n)
  | .fvar i args     => go args (.fvar i)
  | .bvar i args     => go args (.bvar i)
  | .proj n i e args => go args (.proj n i e)
  | _ => [lambdas.repeat .lam e]
section MonadArray

/-- I define the instance `Monad Array` locally for convenience. -/
local instance : Monad List where
  pure a   := [a]
  bind a f := a.bind f

/-- given `e : DTExpr`, returns all η-reduced forms of `e`. -/
partial def getEtas (e : DTExpr) : List DTExpr :=
  match e with
  | .lam .. =>
    e.withLambdas fun n e => do
    let (e, stars) := dropStars n e
    let e ← getEtas e
    reEta n stars e
  | .const n args => (getEtasArray args).map (.const n)
  | .fvar i args => (getEtasArray args).map (.fvar i)
  | .bvar i args => (getEtasArray args).map (.bvar i)
  | .proj n i e args => (getEtas e) >>= ((getEtasArray args).map $ .proj n i ·)
  | .«forall» d b => (getEtas d) >>= ((getEtas b).map $ .«forall» ·)
  | _ => [e]
where
  getEtasArray : Array DTExpr → List (Array DTExpr) :=
    Array.mapM getEtas


end MonadArray

structure Reindex.State where
  stars : Array Nat := #[]
  fvars : Array Nat := #[]

def Reindex.step : Key → Reindex.State → Key × Reindex.State
  | .star i, s => match s.stars.findIdx? (· == i) with
    | some j => (.star j, s)
    | none => (.star s.stars.size, {s with stars := s.stars.push i})
  | .fvar i a, s => match s.fvars.findIdx? (· == i) with
    | some j => (.fvar j a, s)
    | none => (.fvar s.fvars.size a, {s with fvars := s.fvars.push i})
  | k, s => (k, s)

def reindex (keys : Array Key) : Array Key :=
  (keys.mapM (m := StateM Reindex.State) Reindex.step).run' {}




/-- The discrimination tree ignores implicit arguments and proofs.
   We use the following auxiliary id as a "mark". -/
private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar := mkMVar tmpMVarId


structure Flatten.State where
  stars : Array MVarId := #[]
  fvars : Array FVarId := #[]

def getFVar (fvarId : FVarId) : StateM Flatten.State Nat :=
  modifyGet fun s =>
  match s.fvars.findIdx? (· == fvarId) with
  | some idx => (idx, s)
  | none => (s.fvars.size, { s with fvars := s.fvars.push fvarId })
  
def getStar (mvarId : MVarId) : StateM Flatten.State Nat :=
  modifyGet fun s =>
  if mvarId != tmpMVarId then
    if let some idx := s.stars.findIdx? (· == mvarId) then
      (idx, s)
    else
      (s.stars.size, { s with stars := s.stars.push mvarId })
  else
    (s.stars.size, { s with stars := s.stars.push mvarId })
    

private partial def DTExpr.flattenAux (path : Array Key) : DTExpr → StateM Flatten.State (Array Key)
  | .const n args =>   args.foldlM (init := path.push (.const n args.size)) flattenAux
  | .fvar i args => do args.foldlM (init := path.push (.fvar (← getFVar i) args.size)) flattenAux
  | .bvar i args =>    args.foldlM (init := path.push (.bvar i args.size)) flattenAux
  | .star i => return path.push (.star (← getStar i))
  | .lit l => return path.push (.lit l)
  | .sort => return path.push .sort
  | .lam b => flattenAux (path.push .lam) b
  | .«forall» d b => do flattenAux (← flattenAux (path.push .forall) d) b
  | .proj n i e args => do args.foldlM (init := ← flattenAux (path.push (.proj n i args.size)) e) flattenAux

/-- given a `DTExpr`, returns the linearized encoding in terms of `Key`, which is used for `DiscrTree` indexing. -/
def _root_.Tree.DTExpr.flatten (e : DTExpr) (initCapacity := 16) : Array Key :=
  (DTExpr.flattenAux (.mkEmpty initCapacity) e).run' {}

/-- The keys of all proper sub-expressions of the input expression, together with the key of the main expression. -/
partial def DTExpr.flattenSubExprs : DTExpr → StateM Flatten.State (Array Key × Array (Array Key))
  | .const n args => args.foldlM (init := (#[.const n args.size], #[])) fun (path, subExprPaths) arg ↦ do
    let (argPath, argSubExprPaths) ← flattenSubExprs arg
    return (path ++ argPath, (subExprPaths ++ argSubExprPaths).push argPath)
  | .fvar i args => do args.foldlM (init := (#[.fvar (← getFVar i) args.size], #[])) fun (path, subExprPaths) arg ↦ do
    let (argPath, argSubExprPaths) ← flattenSubExprs arg
    return (path ++ argPath, (subExprPaths ++ argSubExprPaths).push argPath) 
  | .bvar i args => args.foldlM (init := (#[.bvar i args.size], #[])) fun (path, subExprPaths) arg ↦ do
    let (argPath, argSubExprPaths) ← flattenSubExprs arg
    return (path ++ argPath, (subExprPaths ++ argSubExprPaths).push argPath) 
  | .star i => do return (#[.star (← getStar i)], #[])
  | .lit l => return (#[.lit l], #[])
  | .sort => return (#[.sort], #[])
  | .lam b => do
    let (bodyPath, bodySubExprsPaths) ← flattenSubExprs b
    return (#[.lam] ++ bodyPath, bodySubExprsPaths.push bodyPath) 
  | .«forall» d b => do
    let (domainPath, domainSubExprsPaths) ← flattenSubExprs d
    let (bodyPath, bodySubExprsPaths) ← flattenSubExprs b
    return (#[.forall] ++ domainPath ++ bodyPath, (domainSubExprsPaths.push domainPath ++ bodySubExprsPaths.push bodyPath)) 
  | .proj n i e args => do 
    let (exprPath, exprSubExprPaths) ← flattenSubExprs e
    args.foldlM (init := (#[.proj n i args.size] ++ exprPath, exprSubExprPaths)) fun (path, subExprPaths) arg ↦ do
    let (argPath, argSubExprPaths) ← flattenSubExprs arg
    return (path ++ argPath, (subExprPaths ++ argSubExprPaths).push argPath) 

/-- 
Because of η-reduction, some expression need to be indexed with multiple different paths
For example, `Continuous fun x => f x + g x` has to be indexed by
`[⟨Continuous, 1⟩, λ, ⟨Hadd.hadd, 6⟩, *0, *0, *0, *1, *2, *3]` and by
`[⟨Continuous, 1⟩, ⟨Hadd.hadd, 5⟩, *0, *0, *0, *1, *2]`.
`etaFlatten` returns all these `Key` indexings.
-/
def _root_.Tree.DTExpr.etaFlatten (e : DTExpr) : List (Array Key) :=
  if hasEta e then (getEtas e).map (·.flatten) else [e.flatten]



-- **Transforming from Expr to DTExpr** 


instance : Inhabited (DiscrTree α) where
  default := {}

private def ignoreArg (a : Expr) (i : Nat) (infos : Array ParamInfo) : MetaM Bool := do
  if h : i < infos.size then
    let info := infos.get ⟨i, h⟩
    if info.isInstImplicit then
      return true
    else if info.isImplicit || info.isStrictImplicit then
      return !(← isType a)
    else
      isProof a
  else
    isProof a

private def ignoreArgs (infos : Array ParamInfo) (args : Array Expr) : MetaM (Array Expr) :=
  args.mapIdxM (fun i arg => return if ← ignoreArg arg i infos then tmpStar else arg)


/--
  Return true if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
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
        loop (e.getArg! 1 3)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then
        return 0
      else
        failure
    | _ => failure


partial def reduce (e : Expr) (config : WhnfCoreConfig) : MetaM Expr := do
  let e ← whnfCore e config
  match (← unfoldDefinition? e) with
  | some e => reduce e config
  | none => match e.etaExpandedStrict? with
    | some e => reduce e config
    | none   => return e


namespace makeInsertionPath
 

private structure Context where
  boundVars : List FVarId := []

private abbrev M := ReaderT Context MetaM

def mkNoindexAnnotation (e : Expr) : Expr :=
  mkAnnotation `noindex e

def hasNoindexAnnotation (e : Expr) : Bool :=
  annotation? `noindex e |>.isSome


partial def mkPathAux (config : WhnfCoreConfig) (e : Expr) : M DTExpr := do
  if hasNoindexAnnotation e then
    return .star tmpMVarId
  else
  let e ← reduce e config
  Expr.withApp e fun fn args => do
  let argPaths : M (Array DTExpr) := do
    let info ← getFunInfoNArgs fn args.size
    let args ← ignoreArgs info.paramInfo args
    args.mapM (mkPathAux config)

  match fn with
  | .const c _ =>
    if let some v := toNatLit? e then
      return .lit v
    return .const c (← argPaths)
  | .proj s i a =>
    let a := if isClass (← getEnv) s then mkNoindexAnnotation a else a
    return .proj s i (← mkPathAux config a) (← argPaths)
  | .fvar fvarId =>
    if let some idx := (← read).boundVars.findIdx? (· == fvarId) then
      return .bvar idx (← argPaths)
    else
      return .fvar fvarId (← argPaths)
  | .mvar mvarId =>
    if (e matches .app ..) then
      return .star tmpMVarId
    else
      return .star mvarId

  | .lam     _ d b _ => return .lam (← mkPathBinder d b config)
  | .forallE _ d b _ => return .forall (← mkPathAux config d) (← mkPathBinder d b config)
  | .lit v      => return .lit v
  | .sort _     => return .sort
  | _           => unreachable!

where
  mkPathBinder (domain body : Expr) (config : WhnfCoreConfig) : M DTExpr := do
    withLocalDeclD `_a domain fun fvar =>
      withReader (fun c => { boundVars := fvar.fvarId! :: c.boundVars }) do
        mkPathAux config (body.instantiate1 fvar)

end makeInsertionPath

def mkDTExpr (e : Expr) (config : WhnfCoreConfig := {}) : MetaM DTExpr :=
  withReducible do makeInsertionPath.mkPathAux config e |>.run {}

-- def mkPath (e : Expr) (config : WhnfCoreConfig := {}) : MetaM (Array Key) :=
--   DTExpr.flatten <$> mkDTExpr e config


-- **Inserting intro a DiscrTree**

/-- Smart `Trie.path` constructor that only adds the path if it is non-empty. -/
private def mkPath (keys : Array Key) (child : Trie α) :=
  if keys.isEmpty then child else Trie.path keys child

private partial def mkFreshPath (keys : Array Key) (value : α) (i : Nat) : Trie α :=
  mkPath keys[i:] (.values #[value])

private def mkNode2 (k1 : Key) (t1 : Trie α) (k2 : Key) (t2 : Trie α) : Trie α :=
  if k1 < k2 then
    .node #[(k1, t1), (k2, t2)]
  else
    .node #[(k2, t2), (k1, t1)]
/--
Note: I have removed this equality check as it doesn't seem to be necessary for now.

If `vs` contains an element `v'` such that `v == v'`, then replace `v'` with `v`.
Otherwise, push `v`.
See issue #2155
Recall that `BEq α` may not be Lawful.
-/
private def insertVal [BEq α] (vs : Array α) (v : α) : Array α :=
  loop 0
where
  loop (i : Nat) : Array α :=
    if h : i < vs.size then
      if v == vs[i] then
        vs.set ⟨i,h⟩ v
      else
        loop (i+1)
    else
      vs.push v
termination_by loop i => vs.size - i


private partial def insertInTrie [BEq α] (keys : Array Key) (v : α) (i : Nat) : Trie α → Trie α
  | .node cs =>
      let k := keys[i]!
      let c := Id.run $ cs.binInsertM
        (fun a b => a.1 < b.1)
        (fun (k', s) => (k', insertInTrie keys v (i+1) s))
        (fun _ => (k, mkFreshPath keys v (i+1)))
        (k, default)
      .node c
  | .values vs =>
      .values (insertVal vs v)
  | .path ks c => Id.run do
    for n in [:ks.size] do
      let k1 := keys[i+n]!
      let k2 := ks[n]!
      if k1 != k2 then
        let shared := ks[:n]
        let rest := ks[n+1:]
        return mkPath shared (mkNode2 k1 (mkFreshPath keys v (i+n+1)) k2 (mkPath rest c))
    return .path ks (insertInTrie keys v (i + ks.size) c)

def insertInDiscrTree [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  let k := keys[0]!
  match d.root.find? k with
  | none =>
    let c := mkFreshPath keys v 1
    { root := d.root.insert k c }
  | some c =>
    let c := insertInTrie keys v 1 c
    { root := d.root.insert k c }

def insertDTExpr [BEq α] (d : DiscrTree α) (e : DTExpr) (v : α) : DiscrTree α :=
  (e.etaFlatten).foldl (init := d) (insertInDiscrTree · · v)

-- def insert [BEq α] (d : DiscrTree α) (e : Expr) (v : α) (config : WhnfCoreConfig) : MetaM (DiscrTree α) := do
--   let key ← mkDTExpr e config
--   return d.insertDTExpr key v






-- **Retrieving from a DiscrTree**

private structure State where
  fvars : Array FVarId := #[]

private structure Context where
  boundVars : List FVarId := []

private abbrev M := ReaderT Context StateRefT State MetaM

def setNewFVar (fvarId : FVarId) (arity : Nat) : M Key :=
  modifyGet fun s =>
  (.fvar s.fvars.size arity, {s with fvars := s.fvars.push fvarId : State})

/-- note that the returned arguments are not valid when the key is a `λ` or `∀`. -/
private def getKeyArgs (e : Expr) (root : Bool) : M (Key × Array Expr) := do
  match e.getAppFn with
  | .const c _     =>
    unless root do
      if let some v := toNatLit? e then
        return (.lit v, #[])
    let nargs := e.getAppNumArgs
    return (.const c nargs, e.getAppRevArgs)
  | .fvar fvarId   =>
    let nargs := e.getAppNumArgs
    if let some i := (← read).boundVars.findIdx? (· == fvarId) then
      return (.bvar i nargs, e.getAppRevArgs)
    if let some i := (← get).fvars.findIdx? (· == fvarId) then
      return (.fvar i nargs, e.getAppRevArgs)
    return (← setNewFVar fvarId nargs, e.getAppRevArgs)
  | .proj s i a .. =>
    let nargs := e.getAppNumArgs
    return (.proj s i nargs, #[a] ++ e.getAppRevArgs)
  | .lit v         => return (.lit v,  #[])
  | .mvar ..       => return (.star 0, #[]) -- for now we ignore the index in stars in the target.
  | .lam ..        => return (.lam,    #[])
  | .forallE ..    => return (.forall, #[])
  | _              => return (.sort,   #[])

private abbrev findKey (cs : Array (Key × Trie α)) (k : Key) : Option (Trie α) :=
  Prod.snd <$> cs.binSearch (k, default) (fun a b => a.1 < b.1)

private def children : Trie α → Array (Key × Trie α)
| .node cs => cs
| .path ks c => #[(ks[0]!, mkPath ks[1:] c)]
| .values _ => panic! "did not expect .values constructor"

section MonadArray

/-- I define the instances `Monad Array` and `Monad m → Monad (ArrayT m)` locally for convenience. -/
local instance : Monad Array where
  pure a   := #[a]
  bind a f := a.concatMap f

private def ArrayT (m : Type u → Type v) a := m (Array a)

local instance [Monad m] : Monad (ArrayT m) where
  pure a := pure (f := m) #[a]
  bind a f := bind (m := m) a (Array.concatMapM f)

partial def skipEntries : Nat → Trie α → Array (Trie α)
  | 0     , t => #[t]
  | skip+1, t => do
    let (k, c) ← children t
    skipEntries (skip + k.arity) c

mutual
  private partial def findExpr (config : WhnfCoreConfig) (e : Expr) : (Trie α × HashMap Nat Expr × Nat) → M (Array (Trie α × HashMap Nat Expr × Nat))
  | (c, assignments, score) => do
    let cs := children c
    let e ← reduce e config
    let (k, args) ← getKeyArgs e (root := false)

    let visitStars (start : Array (Trie α × HashMap Nat Expr × Nat)) : M (Array (Trie α × HashMap Nat Expr × Nat)) := do
      let mut result := start
      for (k, c) in cs do
        match k with
        | .star i =>
          match assignments.find? i with
          | some assignment =>
            let s ← (saveState : MetaM _)
            if ← (try isDefEq e assignment catch _ => return false) then
              s.restore
              result := result.push (c, assignments, score+1)
          | none =>
            result := result.push (c, assignments.insert i e, score)
        | _ => break
      return result

    match k with
    | .star _ => return cs.concatMap fun (k, c) => (skipEntries k.arity c).map (·, assignments, score)
    | .fvar _ _ => visitStars #[]
    | _       => visitStars =<< match findKey cs k with
      | none   => return #[]
      | some c => match k with
        | .lam    => findBoundExpr e.bindingDomain! e.bindingBody! config (c, assignments, score)
        | .forall => show ArrayT M _ from findExpr config e.bindingDomain! (c, assignments, score+1) >>= findBoundExpr e.bindingDomain! e.bindingBody! config
        | _ => findExprs args config (c, assignments, score+1)

  private partial def findExprs (args : Array Expr) (config : WhnfCoreConfig) : (Trie α × HashMap Nat Expr × Nat) → ArrayT M (Trie α × HashMap Nat Expr × Nat) :=
    args.foldrM (findExpr config)

  private partial def findBoundExpr (domain body : Expr) (config : WhnfCoreConfig) : (Trie α × HashMap Nat Expr × Nat) → M (Array (Trie α × HashMap Nat Expr × Nat)) :=
    (withLocalDeclD `_a domain fun fvar =>
    withReader (fun {boundVars,} => ⟨fvar.fvarId! :: boundVars⟩) $ findExpr config (body.instantiate1 fvar) ·)

end
/-- return the results from the DiscrTree that match the given expression, together with their matching scores. -/
partial def getUnifyWithScore (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) : MetaM (Array (Array α × Nat)) :=
  withReducible do
    let e ← reduce e config
    let (k, args) ← getKeyArgs e (root := true) |>.run {} |>.run' {}
    match k with
    | .star _ => return #[] --throwError "the unification pattern is a metavariable, so it cannot be used for a search"
    | _ =>
      let result ← match d.root.find? k with
        | none   => pure #[]
        | some c => (match k with
          | .lam    => findBoundExpr e.bindingDomain! e.bindingBody! config (c, {}, 0)
          | .forall => show ArrayT M _ from findExpr config e.bindingDomain! (c, {}, 1) >>= findBoundExpr e.bindingDomain! e.bindingBody! config
          | _ => findExprs args config (c, {}, 1)) |>.run {} |>.run' {}
      let result := result.map fun | (.values vs, _, n) => (vs, n) | _ => panic! "resulting Trie is not .values"
      match d.root.find? (.star 0) with
      | some (.values vs) => return result.push (vs, 0)
      | _ => return result

end MonadArray
/-- apply `getUnifyWithScore` at the given subexrpession. -/
def getSubExprUnify (d : DiscrTree α) (tree : Expr) (treePos : OuterPosition) (pos : InnerPosition) (config : WhnfCoreConfig := {}) : MetaM (Array (Array α × Nat)) := do
  withTreeSubexpr tree treePos pos fun _ e => getUnifyWithScore d e config

/-- Filter the matches coming from `getUnifyWithScore` by whether the `filter` function succeeds within the given `maxHeartbeats`.-/
def filterLibraryResults («matches» : Array (Array α × Nat)) (filter : α → MetaM Unit) (max_results : Option Nat := some 18)
    (maxHeartbeats : Nat := 1000) (maxTotalHeartbeats : Nat := 10000) : MetaM (Array (Array α × Nat)) := do
  let numHeartbeats ← IO.getNumHeartbeats
  let maxTotalHeartbeats := maxTotalHeartbeats * 1000
  let filter a := Aesop.withMaxHeartbeats maxHeartbeats do
    try
      filter a
      return true
    catch _ => 
      return false

  let «matches» := «matches».qsort (·.2 > ·.2)
  let mut result := #[]
  let mut num_results := 0
  
  for (candidates, score) in «matches» do
    if max_results.elim false (num_results ≥ ·) || (← IO.getNumHeartbeats) - numHeartbeats > maxTotalHeartbeats then
      return result

    let mut filtered := #[]
    for candidate in candidates do
      if max_results.elim false (num_results ≥ ·) || (← IO.getNumHeartbeats) - numHeartbeats > maxTotalHeartbeats then
        break
      if ← filter candidate then
        filtered := filtered.push candidate
        num_results := num_results + 1

    unless filtered.isEmpty do
      result := result.push (filtered, score)
  return result

variable {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
partial def Trie.mapArraysM (t : DiscrTree.Trie α) (f : Array α → m (Array β)) :
    m (Trie β) := do
  match t with
  | .node children =>
    return .node (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))
  | .values vs =>
    return .values (← f vs)
  | .path ks c =>
    return .path ks (← c.mapArraysM f)

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
def mapArraysM (d : DiscrTree α) (f : Array α → m (Array β)) : m (DiscrTree β) := do
  pure { root := ← d.root.mapM (fun t => t.mapArraysM f) }

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α) (f : Array α → Array β) : DiscrTree β :=
  d.mapArraysM fun A => (pure (f A) : Id (Array β))

