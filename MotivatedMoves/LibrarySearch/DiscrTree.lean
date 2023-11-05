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
  | .other    => 1
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
  | .other                  => "◾"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .const k _              => Std.format k
  | .proj s i _             => Std.format s ++ "." ++ Std.format i
  | .fvar k _               => Std.format k
  | .bvar i _               => "#" ++ Std.format i
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
    "node" ++ Format.join (cs.toList.map fun ⟨k, c⟩ => Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))
  | .values vs => "values" ++ if vs.isEmpty then Format.nil else " " ++ Std.format vs
  | .path ks c => "path " ++ Std.format ks ++ " => " ++ format c
  

instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩

partial def format [ToFormat α] (d : DiscrTree α) : Format :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × Format) k c =>
      (false, p.2 ++ (if p.1 then Format.nil else Format.line) ++ Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (DiscrTree α) := ⟨format⟩

/-- The discrimination tree ignores implicit arguments and proofs.
   We use the following auxiliary id as a "mark". -/
private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar := mkMVar tmpMVarId

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

private partial def pushArgsAux (infos : Array ParamInfo) (config : WhnfCoreConfig) : Nat → Expr → Array Expr → MetaM (Array Expr)
  | i, .app f a, todo => do
    if (← ignoreArg a i infos) then
      pushArgsAux infos config (i-1) f (todo.push tmpStar)
    else
      pushArgsAux infos config (i-1) f (todo.push a)
  | _, _, todo => return todo

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
        loop (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then
        return 0
      else
        failure
    | _ => failure


def mkNoindexAnnotation (e : Expr) : Expr :=
  mkAnnotation `noindex e

def hasNoindexAnnotation (e : Expr) : Bool :=
  annotation? `noindex e |>.isSome

partial def reduceDT (e : Expr) (config : WhnfCoreConfig) : MetaM Expr := do
  let e ← whnfCore e config
  match (← unfoldDefinition? e) with
  | some e => reduceDT e config
  | none => match e.etaExpandedStrict? with
    | some e => reduceDT e config
    | none   => return e

namespace makeInsertionPath

private structure State where
  mvarNums : HashMap MVarId Nat := {}
  mvarCount : Nat := 0
  fvarNums : HashMap FVarId Nat := {}
  fvarCount : Nat := 0

private structure Context where
  boundVars : List FVarId := []

private abbrev M := ReaderT Context StateRefT State MetaM

def setNewStar (mvarId : Option MVarId) : M Key := do
  let s ← get
  set {s with mvarCount := s.mvarCount + 1, mvarNums := mvarId.elim s.mvarNums (s.mvarNums.insert · s.mvarCount)}
  return .star s.mvarCount

def setNewFVar (fvarId : FVarId) (arity : Nat) : M Key := do
  let s ← get
  set {s with fvarCount := s.fvarCount + 1, fvarNums := s.fvarNums.insert fvarId s.fvarCount : State}
  return .fvar s.fvarCount arity

private def getPathArgs (root : Bool) (e : Expr) (config : WhnfCoreConfig) : M (Key × Array Expr) := do
    let fn := e.getAppFn
    let push (k : Key) (nargs : Nat) (args : Array Expr) : M (Key × Array Expr) := do
      let info ← getFunInfoNArgs fn nargs
      let args ← pushArgsAux info.paramInfo config (nargs-1) e args
      return (k, args)
    match fn with
    | .const c _ =>
      unless root do
        if let some v := toNatLit? e then
          return (.lit v, #[])
        -- if (← shouldAddAsStar c e) then
        --   return (.star, todo)
      let nargs := e.getAppNumArgs
      push (.const c nargs) nargs #[]
    | .proj s i a =>
      let a := if isClass (← getEnv) s then mkNoindexAnnotation a else a
      let nargs := e.getAppNumArgs
      push (.proj s i nargs) nargs #[a]
    | .fvar fvarId =>
      let nargs := e.getAppNumArgs
      if let some i := (← read).boundVars.findIdx? (· == fvarId) then
        push (.bvar i nargs) nargs #[]
      else if let some i := (← get).fvarNums.find? fvarId then
        push (.fvar i nargs) nargs #[]
      else
      push (← setNewFVar fvarId nargs) nargs #[]
    | .mvar mvarId =>
      if (e matches .app ..) || mvarId == tmpMVarId then
        (·, #[]) <$> setNewStar none
      else do
      if let some i := (← get).mvarNums.find? mvarId then
        pure (.star i, #[])
      else (·, #[]) <$> setNewStar mvarId

    | .lit v     => return (.lit v,  #[])
    | .lam ..    => return (.lam,    #[])
    | .forallE ..=> return (.forall, #[])
    | _          => return (.other,  #[])

mutual
  partial def mkPathAux (root : Bool) (config : WhnfCoreConfig) (e : Expr) (keys : Array Key) : M (Array Key) := do
    if hasNoindexAnnotation e then
      keys.push <$> setNewStar none
    else
    let e ← reduceDT e config
    let (k, args) ← getPathArgs root e config
    match k with
    | .lam    => mkPathBinder e.bindingDomain! e.bindingBody! config (keys.push k)
    | .forall => do
      let keys ← mkPathAux false config e.bindingDomain! (keys.push k)
      mkPathBinder e.bindingDomain! e.bindingBody! config keys
    | _ =>
      args.foldrM (init := keys.push k) (mkPathAux false config)

  partial def mkPathBinder (domain body : Expr) (config : WhnfCoreConfig) (keys : Array Key) : M (Array Key) := do
    withLocalDeclD `_a domain fun fvar =>
      withReader (fun c => { boundVars := fvar.fvarId! :: c.boundVars }) do
        mkPathAux false config (body.instantiate1 fvar) keys
end
end makeInsertionPath

private def initCapacity := 8

def mkPath (e : Expr) (config : WhnfCoreConfig := {}) : MetaM (Array Key) := do
  withReducible do makeInsertionPath.mkPathAux (root := true) config e (.mkEmpty initCapacity) |>.run {} |>.run' {}

private def nonemptyPath (keys : Array Key) (child : Trie α) :=
  if keys.isEmpty then child else .path keys child

private partial def createPath (keys : Array Key) (v : α) (i : Nat) : Trie α :=
  nonemptyPath keys[i:] (.values #[v])

/--
Note: I have removed this equality check as it doesn't seem to be necessary, but in the future this might change.

If `vs` contains an element `v'` such that `v == v'`, then replace `v'` with `v`.
Otherwise, push `v`.
See issue #2155
Recall that `BEq α` may not be Lawful.
-/
private def insertVal [BEq α] (vs : Array α) (v : α) : Array α :=
  vs.push v--loop 0
-- where
--   loop (i : Nat) : Array α :=
--     if h : i < vs.size then
--       if v == vs[i] then
--         vs.set ⟨i,h⟩ v
--       else
--         loop (i+1)
--     else
--       vs.push v
-- termination_by loop i => vs.size - i

private partial def insertAux [BEq α] (keys : Array Key) (v : α) (i : Nat) : Trie α → Trie α
  | .node cs =>
      let k := keys[i]!
      let c := Id.run $ cs.binInsertM
        (fun a b => a.1 < b.1)
        (fun (_, s) => let c := insertAux keys v (i+1) s; (k, c))
        (fun _ => let c := createPath keys v (i+1); (k, c))
        (k, default)
      .node c
  | .values vs =>
      .values (insertVal vs v)
  | .path ks c => Id.run do
    for n in [:ks.size] do
      if ks[n]! != keys[i+n]! then
        let shared := ks[:n]
        let k := ks[n]!
        let rest := ks[n+1:]
        return nonemptyPath shared (insertAux keys v (i+n) (.node #[(k, nonemptyPath rest c)]))
    return .path ks (insertAux keys v (i + ks.size) c)

def insertCore [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]!
    match d.root.find? k with
    | none =>
      let c := createPath keys v 1
      { root := d.root.insert k c }
    | some c =>
      let c := insertAux keys v 1 c
      { root := d.root.insert k c }

def insert [BEq α] (d : DiscrTree α) (e : Expr) (v : α) (config : WhnfCoreConfig) : MetaM (DiscrTree α) := do
  let keys ← mkPath e config
  return d.insertCore keys v


private structure State where
  fvarNums : HashMap FVarId Nat := {}
  fvarCount : Nat := 0

private structure Context where
  boundVars : List FVarId := []

private abbrev M := ReaderT Context StateRefT State MetaM

def setNewFVar (fvarId : FVarId) (arity : Nat) : M Key := do
  let s ← get
  set {s with fvarCount := s.fvarCount + 1, fvarNums := s.fvarNums.insert fvarId s.fvarCount : State}
  return .fvar s.fvarCount arity

/- note that the returned arguments are not valid when the key is a `λ` or `∀`. -/
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
    if let some i := (← get).fvarNums.find? fvarId then
      return (.fvar i nargs, e.getAppRevArgs)
    return (← setNewFVar fvarId nargs, e.getAppRevArgs)
  | .proj s i a .. =>
    let nargs := e.getAppNumArgs
    return (.proj s i nargs, #[a] ++ e.getAppRevArgs)
  | .lit v         => return (.lit v,  #[])
  | .mvar ..       => return (.star 0, #[]) -- for now we ignore the index in stars in the target.
  | .lam ..        => return (.lam,    #[])
  | .forallE ..    => return (.forall, #[])
  | _              => return (.other,  #[])

private abbrev findKey (cs : Array (Key × Trie α)) (k : Key) : Option (Trie α) :=
  Prod.snd <$> cs.binSearch (k, default) (fun a b => a.1 < b.1)

private def children : Trie α → Array (Key × Trie α)
| .node cs => cs
| .path ks c => #[(ks[0]!, nonemptyPath ks[1:] c)]
| .values _ => panic! "did not expect .values constructor"

section MonadArray

/- I define the instances `Monad Array` and `Monad m → Monad (ArrayT m)` locally for convenience. -/
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
    let e ← reduceDT e config
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
    let e ← reduceDT e config
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
def getSubExprUnify (d : DiscrTree α) (tree : Expr) (treePos : OuterPosition) (pos : InnerPosition) (config : WhnfCoreConfig := {beta := false}) : MetaM (Array (Array α × Nat)) := do
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

