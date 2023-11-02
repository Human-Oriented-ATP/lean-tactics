import MotivatedMoves.LibrarySearch.DiscrTreeTypes
import MotivatedMoves.ProofState.Tree

namespace Tree.DiscrTree

open Lean Meta DiscrTree

/-!
things to add:
give a score for a match from isDefEq, instead of always being 1?
When replacing instances with a star, make sure that multiple of the same instance become the same star.


  (Imperfect) discrimination trees.
  We use a hybrid representation.
  - A `PersistentHashMap` for the root node which usually contains many children.
  - A sorted array of key/node pairs for inner nodes.

  The edges are labeled by keys:
  - Constant names (and arity). Universe levels are ignored.
  - Free variables (and arity). Thus, an entry in the discrimination tree
    may reference hypotheses from the local context.
  - Literals
  - Star/Wildcard. We use them to represent metavariables and terms
    we want to ignore. We ignore implicit arguments and proofs.
  - Other. We use to represent other kinds of terms (e.g., nested lambda, forall, sort, etc).

  We reduce terms using `TransparencyMode.reducible`. Thus, all reducible
  definitions in an expression `e` are unfolded before we insert it into the
  discrimination tree.

  Recall that projections from classes are **NOT** reducible.
  For example, the expressions `Add.add α (ringAdd ?α ?s) ?x ?x`
  and `Add.add Nat Nat.hasAdd a b` generates paths with the following keys
  respctively
  ```
  ⟨Add.add, 4⟩, *, *, *, *
  ⟨Add.add, 4⟩, *, *, ⟨a,0⟩, ⟨b,0⟩
  ```

  That is, we don't reduce `Add.add Nat inst a b` into `Nat.add a b`.
  We say the `Add.add` applications are the de-facto canonical forms in
  the metaprogramming framework.
  Moreover, it is the metaprogrammer's responsibility to re-pack applications such as
  `Nat.add a b` into `Add.add Nat inst a b`.

  Remark: we store the arity in the keys
  1- To be able to implement the "skip" operation when retrieving "candidate"
     unifiers.
  2- Distinguish partial applications `f a`, `f a b`, and `f a b c`.
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

instance : Inhabited (Trie α s) := ⟨.node #[] #[]⟩

def empty : DiscrTree α s := { root := {} }

partial def Trie.format [ToFormat α] : Trie α s → Format
  | .node vs cs => Format.group $ Format.paren $
    "node" ++ (if vs.isEmpty then Format.nil else " " ++ Std.format vs)
    ++ Format.join (cs.toList.map fun ⟨k, c⟩ => Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))

instance [ToFormat α] : ToFormat (Trie α s) := ⟨Trie.format⟩

partial def format [ToFormat α] (d : DiscrTree α s) : Format :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × Format) k c =>
      (false, p.2 ++ (if p.1 then Format.nil else Format.line) ++ Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (DiscrTree α s) := ⟨format⟩

/-- The discrimination tree ignores implicit arguments and proofs.
   We use the following auxiliary id as a "mark". -/
private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar := mkMVar tmpMVarId

instance : Inhabited (DiscrTree α s) where
  default := {}

/--
  Return true iff the argument should be treated as a "wildcard" by the discrimination tree.

  - We ignore proofs because of proof irrelevance. It doesn't make sense to try to
    index their structure.

  - We ignore instance implicit arguments (e.g., `[Add α]`) because they are "morally" canonical.
    Moreover, we may have many definitionally equal terms floating around.
    Example: `Ring.hasAdd Int Int.isRing` and `Int.hasAdd`.

  - We considered ignoring implicit arguments (e.g., `{α : Type}`) since users don't "see" them,
    and may not even understand why some simplification rule is not firing.
    However, in type class resolution, we have instance such as `Decidable (@Eq Nat x y)`,
    where `Nat` is an implicit argument. Thus, we would add the path
    ```
    Decidable -> Eq -> * -> * -> * -> [Nat.decEq]
    ```
    to the discrimination tree IF we ignored the implict `Nat` argument.
    This would be BAD since **ALL** decidable equality instances would be in the same path.
    So, we index implicit arguments if they are types.
    This setting seems sensible for simplification theorems such as:
    ```
    forall (x y : Unit), (@Eq Unit x y) = true
    ```
    If we ignore the implicit argument `Unit`, the `DiscrTree` will say it is a candidate
    simplification theorem for any equality in our goal.

  Remark: if users have problems with the solution above, we may provide a `noIndexing` annotation,
  and `ignoreArg` would return true for any term of the form `noIndexing t`.
-/
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

private partial def pushArgsAux (infos : Array ParamInfo) : Nat → Expr → Array Expr → MetaM (Array Expr)
  | i, .app f a, todo => do
    if (← ignoreArg a i infos) then
      pushArgsAux infos (i-1) f (todo.push tmpStar)
    else
      pushArgsAux infos (i-1) f (todo.push a)
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

/--
  TODO: add hook for users adding their own functions for controlling `shouldAddAsStar`
  Different `DiscrTree` users may populate this set using, for example, attributes.

  Remark: we currently tag "offset" terms as star to avoid having to add special
  support for offset terms.
  Example, suppose the discrimination tree contains the entry
  `Nat.succ ?m |-> v`, and we are trying to retrieve the matches for `Expr.lit (Literal.natVal 1) _`.
  In this scenario, we want to retrieve `Nat.succ ?m |-> v`
-/
private def shouldAddAsStar (_fName : Name) (_e : Expr) : MetaM Bool := do
  return false --isOffset fName e

def mkNoindexAnnotation (e : Expr) : Expr :=
  mkAnnotation `noindex e

def hasNoindexAnnotation (e : Expr) : Bool :=
  annotation? `noindex e |>.isSome

/--
Reduction procedure for the discrimination tree indexing.
The parameter `simpleReduce` controls how aggressive the term is reduced.
The parameter at type `DiscrTree` controls this value.
See comment at `DiscrTree`.
-/
partial def reduceDT (e : Expr) (simpleReduce : Bool) : MetaM Expr := do
  let e ← whnfCore e (simpleReduceOnly := simpleReduce)
  match (← unfoldDefinition? e) with
  | some e => reduceDT e simpleReduce
  | none => match e.etaExpandedStrict? with
    | some e => reduceDT e simpleReduce
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

/- Remark: we use `shouldAddAsStar` only for nested terms, and `root == false` for nested terms -/
private def getPathArgs (root : Bool) (e : Expr) : M (Key × Array Expr) := do
    let fn := e.getAppFn
    let push (k : Key) (nargs : Nat) (args : Array Expr) : M (Key × Array Expr) := do
      let info ← getFunInfoNArgs fn nargs
      let args ← pushArgsAux info.paramInfo (nargs-1) e args
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
      /-
      If `s` is a class, then `a` is an instance. Thus, we annotate `a` with `no_index` since we do not
      index instances. This should only happen if users mark a class projection function as `[reducible]`.

      TODO: add better support for projections that are functions
      -/
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
  partial def mkPathAux (root : Bool) (simpleReduce : Bool) (e : Expr) (keys : Array Key) : M (Array Key) := do
    if hasNoindexAnnotation e then
      keys.push <$> setNewStar none
    else
    let e ← reduceDT e simpleReduce
    let (k, args) ← getPathArgs root e     
    match k with
    | .lam    => mkPathBinder e.bindingDomain! e.bindingBody! simpleReduce (keys.push k)
    | .forall => do
      let keys ← mkPathAux false simpleReduce e.bindingDomain! (keys.push k)
      mkPathBinder e.bindingDomain! e.bindingBody! simpleReduce keys
    | _ =>
      args.foldrM (init := keys.push k) (mkPathAux false simpleReduce)

  partial def mkPathBinder (domain body : Expr) (simpleReduce : Bool) (keys : Array Key) : M (Array Key) := do
    withLocalDeclD `_a domain fun fvar =>
      withReader (fun c => { boundVars := fvar.fvarId! :: c.boundVars }) do
        mkPathAux false simpleReduce (body.instantiate1 fvar) keys
end
end makeInsertionPath

private def initCapacity := 8

def mkPath (e : Expr) (simpleReduce := true) : MetaM (Array Key) := do
  withReducible do makeInsertionPath.mkPathAux (root := true) simpleReduce e (.mkEmpty initCapacity) |>.run {} |>.run' {}

private partial def createNodes (keys : Array Key) (v : α) (i : Nat) : Trie α s :=
  if h : i < keys.size then
    let k := keys.get ⟨i, h⟩
    let c := createNodes keys v (i+1)
    .node #[] #[(k, c)]
  else
    .node #[v] #[]

/--
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

private partial def insertAux [BEq α] (keys : Array Key) (v : α) : Nat → Trie α s → Trie α s
  | i, .node vs cs =>
    if h : i < keys.size then
      let k := keys.get ⟨i, h⟩
      let c := Id.run $ cs.binInsertM
          (fun a b => a.1 < b.1)
          (fun ⟨_, s⟩ => let c := insertAux keys v (i+1) s; (k, c)) -- merge with existing
          (fun _ => let c := createNodes keys v (i+1); (k, c))
          (k, default)
      .node vs c
    else
      .node (insertVal vs v) cs

def insertCore [BEq α] (d : DiscrTree α s) (keys : Array Key) (v : α) : DiscrTree α s :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]!
    match d.root.find? k with
    | none =>
      let c := createNodes keys v 1
      { root := d.root.insert k c }
    | some c =>
      let c := insertAux keys v 1 c
      { root := d.root.insert k c }

def insert [BEq α] (d : DiscrTree α s) (e : Expr) (v : α) : MetaM (DiscrTree α s) := do
  let keys ← mkPath e s
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

private abbrev findKey (cs : Array (Key × Trie α s)) (k : Key) : Option (Trie α s) :=
  Prod.snd <$> cs.binSearch (k, default) (fun a b => a.1 < b.1)

private instance : Monad Array where
  pure a   := #[a]
  bind a f := a.concatMap f

partial def skipEntries : Nat → Trie α s → Array (Trie α s)
  | skip+1, .node _ cs => do 
    let (k, c) ← cs
    skipEntries (skip + k.arity) c
  | 0     , c          => #[c]

private def ArrayT (m : Type u → Type v) a := m (Array a)

private instance [Monad m] : Monad (ArrayT m) where
  pure a := pure (f := m) #[a]
  bind a f := bind (m := m) a (Array.concatMapM f)

mutual
  private partial def findExpr (e : Expr) : (Trie α s × HashMap Nat Expr × Nat) → M (Array (Trie α s × HashMap Nat Expr × Nat))
  | (.node _ cs, assignments, score) => do
    let e ← reduceDT e (simpleReduce := s)
    let (k, args) ← getKeyArgs e (root := false)

    let visitStars (start : Array (Trie α s × HashMap Nat Expr × Nat)) : M (Array (Trie α s × HashMap Nat Expr × Nat)) := do
      let mut result := start
      for (k, v) in cs do
        match k with
        | .star i =>
          match assignments.find? i with
          | some assignment =>
            let s ← (saveState : MetaM _)
            if ← (try isDefEq e assignment catch _ => return false) then
              s.restore
              result := result.push (v, assignments, score+1)
          | none =>
            result := result.push (v, assignments.insert i e, score)
        | _ => break
      return result

    match k with
    | .star _ => return cs.concatMap fun (k, c) => (skipEntries k.arity c).map (·, assignments, score)
    | .fvar _ _ => visitStars #[]
    | _       => visitStars =<< match findKey cs k with
      | none   => return #[]
      | some c => match k with
        | .lam    => findBoundExpr e.bindingDomain! e.bindingBody! (c, assignments, score)
        | .forall => show ArrayT M _ from findExpr e.bindingDomain! (c, assignments, score+1) >>= findBoundExpr e.bindingDomain! e.bindingBody!
        | _ => findExprs args (c, assignments, score+1)

  private partial def findExprs (args : Array Expr) : (Trie α s × HashMap Nat Expr × Nat) → ArrayT M (Trie α s × HashMap Nat Expr × Nat) :=
    args.foldrM findExpr

  private partial def findBoundExpr (domain body : Expr) : (Trie α s × HashMap Nat Expr × Nat) → M (Array (Trie α s × HashMap Nat Expr × Nat)) :=
    (withLocalDeclD `_a domain fun fvar =>
    withReader (fun {boundVars,} => ⟨fvar.fvarId! :: boundVars⟩) $ findExpr (body.instantiate1 fvar) ·)

end

partial def getUnifyWithSpecificity (d : DiscrTree α s) (e : Expr) : MetaM (Array (Array α × Nat)) :=
  withReducible do
    let e ← reduceDT e (simpleReduce := s)
    let (k, args) ← getKeyArgs e (root := true) |>.run {} |>.run' {}
    match k with
    | .star _ => return #[] --throwError "the unification pattern is a metavariable, so it cannot be used for a search"
    | _ =>
      let result ← match d.root.find? k with
        | none   => pure #[]
        | some c => (match k with
          | .lam    => findBoundExpr e.bindingDomain! e.bindingBody! (c, {}, 0)
          | .forall => show ArrayT M _ from findExpr e.bindingDomain! (c, {}, 1) >>= findBoundExpr e.bindingDomain! e.bindingBody!
          | _ => findExprs args (c, {}, 1)) |>.run {} |>.run' {}
      let result := result.map $ fun (.node vs _, _, n) => (vs, n)
      match d.root.find? (.star 0) with
      | none => return result
      | some (.node vs _) => return result.push (vs, 0)


def getSubExprUnify (d : DiscrTree α s) (tree : Expr) (treePos : OuterPosition) (pos : InnerPosition) : MetaM (Array (Array α × Nat)) := do
  withTreeSubexpr tree treePos pos fun _ e => getUnifyWithSpecificity d e


def filterLibraryResults («matches» : Array (Array α × Nat)) (filter : α → MetaM Bool)
    (max_results : Option Nat := some 18) (max_tries : Option Nat := some 40) : MetaM (Array (Array α × Nat)) := do
  let «matches» := «matches».qsort (·.2 > ·.2)
  let mut result := #[]
  let mut num_results : Nat := 0
  let mut num_tries : Nat := 0
  
  for (candidates, score) in «matches» do
    if max_results.elim false (num_results ≥ ·) || max_tries.elim false (num_tries ≥ ·) then
      break

    let mut filtered := #[]
    for candidate in candidates do
      if max_results.elim false (num_results ≥ ·) || max_tries.elim false (num_tries ≥ ·) then
        break
      num_tries := num_tries + 1
      if ← filter candidate then
        filtered := filtered.push candidate
        num_results := num_results + 1
        continue

    unless filtered.isEmpty do
      result := result.push (filtered, score)
  return result

variable {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
partial def Trie.mapArraysM (t : DiscrTree.Trie α s) (f : Array α → m (Array β)) :
    m (Trie β s) := do
  match t with
  | .node vs children =>
    return .node (← f vs) (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
def mapArraysM (d : DiscrTree α s) (f : Array α → m (Array β)) : m (DiscrTree β s) := do
  pure { root := ← d.root.mapM (fun t => t.mapArraysM f) }

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α s) (f : Array α → Array β) : DiscrTree β s :=
  d.mapArraysM fun A => (pure (f A) : Id (Array β))

