import TreeMoves.TreeLemmas

namespace Tree

open Lean

def mkForall (name : Name) (u : Level) (domain : Expr) (body : Expr) : Expr := 
  mkApp2 (.const ``Forall [u]) domain (.lam name domain body .default)
def mkExists (name : Name) (u : Level) (domain : Expr) (body : Expr) : Expr := 
  mkApp2 (.const ``Exists [u]) domain (.lam name domain body .default)

def mkInstance (name : Name) (u : Level) (domain : Expr) (body : Expr) : Expr := 
  mkApp2 (.const ``Instance [u]) domain (.lam name domain body .default)

def mkImp (p q : Expr) : Expr :=
  mkApp2 (.const ``Imp []) p q
def mkAnd (p q : Expr) : Expr :=
  mkApp2 (.const ``And []) p q


@[match_pattern]
def imp_pattern (p q : Expr) : Expr :=
  mkApp2 (.const ``Imp []) p q
@[match_pattern]
def and_pattern (p q : Expr) : Expr :=
  mkApp2 (.const ``And []) p q

@[match_pattern]
def forall_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (body : Expr) {bi : BinderInfo} : Expr :=
  mkApp2 (.const ``Forall [u]) domain' (.lam name domain body bi)
@[match_pattern]
def exists_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (body : Expr) {bi : BinderInfo} : Expr :=
  mkApp2 (.const ``Exists [u]) domain' (.lam name domain body bi)

@[match_pattern]
def instance_pattern (name : Name) (u : Level) (cls : Expr) {cls' : Expr} (body : Expr) {bi : BinderInfo} : Expr :=
  mkApp2 (.const ``Instance [u]) cls' (.lam name cls body bi)


@[match_pattern]
def regular_and_pattern (p q : Expr) : Expr :=
  mkApp2 (.const `And []) p q
@[match_pattern]
def regular_exists_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (body : Expr) (bi : BinderInfo) : Expr :=
  mkApp2 (.const `Exists [u]) domain' (.lam name domain body bi)
@[match_pattern]
def regular_iff_pattern (p q : Expr) : Expr :=
  mkApp2 (.const `Iff []) p q
@[match_pattern]
def eq_pattern (u : Level) (α p q : Expr) : Expr :=
  mkApp3 (.const `Eq [u]) α p q
@[match_pattern]
def regular_or_pattern (p q : Expr) : Expr :=
  mkApp2 (.const `Or []) p q
@[match_pattern]
def regular_not_pattern (p : Expr) : Expr :=
  .app (.const `Not []) p

def isTree : Expr → Bool
| imp_pattern ..
| and_pattern ..
| forall_pattern ..
| exists_pattern ..
| instance_pattern .. => true
| _ => false


structure TreeRecursor (m : Type u → Type v) (α : Type u) where
  all (name : Name) (u : Level) (domain : Expr) : Bool → Expr → (Expr → m α) → OptionT m α
  ex  (name : Name) (u : Level) (domain : Expr) : Bool → Expr → (Expr → m α) → OptionT m α

  imp_right (p : Expr) : Bool → Expr → m α → OptionT m α
  and_right (p : Expr) : Bool → Expr → m α → OptionT m α
  imp_left  (p : Expr) : Bool → Expr → m α → OptionT m α
  and_left  (p : Expr) : Bool → Expr → m α → OptionT m α

  inst (n : Name) (u : Level) (cls : Expr) : Bool → Expr → (Expr → m α) → OptionT m α

instance [Monad m] [MonadNameGenerator m] : EmptyCollection (TreeRecursor m α) where
  emptyCollection := {
    all := fun _ _ _ _ _ k => do k (.fvar (← mkFreshFVarId))
    ex := fun _ _ _ _ _ k => do k (.fvar (← mkFreshFVarId))
    inst := fun _ _ _ _ _ k => do k (.fvar (← mkFreshFVarId))
    imp_left := fun _ _ _ k => k
    imp_right := fun _ _ _ k => k
    and_left := fun _ _ _ k => k
    and_right := fun _ _ _ k => k
  }

inductive TreeBinderKind where
  | imp_right
  | and_right
  | imp_left
  | and_left
  | all
  | ex
  | inst
deriving BEq
instance : ToString TreeBinderKind where
  toString := fun 
    | .imp_right => "· ⇨"
    | .and_right => "· ∧"
    | .imp_left => "⇨ ·"
    | .and_left => "∧ ·"
    | .all => "∀"
    | .ex => "∃"
    | .inst => "[·]"

partial def TreeRecursor.recurse [Inhabited α] [Monad m] [MonadError m] (r : TreeRecursor m α) (pol : Bool := true) (tree : Expr) (path : List TreeBinderKind)
  (k : Bool → Expr → List TreeBinderKind → m α) : m α :=
  let rec visit [Inhabited α] (pol : Bool) (ys : List TreeBinderKind) (e : Expr) : m α :=
    let k? l := do (Option.getDM (← l) (k pol e ys))
    match ys, e with
    | .all      ::xs, forall_pattern n u α b => k? do r.all n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .ex       ::xs, exists_pattern n u α b => k? do r.ex  n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .imp_right::xs, imp_pattern p tree     => k? do r.imp_right p pol tree (visit   pol  xs tree)
    | .and_right::xs, and_pattern p tree     => k? do r.and_right p pol tree (visit   pol  xs tree)
    | .imp_left ::xs, imp_pattern tree p     => k? do r.imp_left  p pol tree (visit (!pol) xs tree)
    | .and_left ::xs, and_pattern tree p     => k? do r.and_left  p pol tree (visit   pol  xs tree)
    | .inst     ::xs, instance_pattern n u α b => k? do r.inst n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | [], e => k pol e []
    | xs, e => throwError m! "could not find a subexpression at {xs} in {e}"
  visit pol path tree

partial def TreeRecursor.recurseNonTree [Inhabited α] [Monad m] [MonadError m] (r : TreeRecursor m α) (pol : Bool := true) (tree : Expr) (path : List TreeBinderKind)
  (k : Bool → Expr → List TreeBinderKind → m α) : m α :=
  let rec visit [Inhabited α] (pol : Bool) (ys : List TreeBinderKind) (e : Expr) : m α :=
    let k? l := do (Option.getDM (← l) (k pol e ys))
    match ys, e with
    | .all      ::xs, .forallE n α b _bi               => k? do r.all n default α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .ex       ::xs, regular_exists_pattern n u α b _ => k? do r.ex  n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .imp_right::xs, .forallE _ p tree _bi            => k? do r.imp_right p pol tree (visit   pol  xs tree)
    | .and_right::xs, regular_and_pattern p tree       => k? do r.and_right p pol tree (visit   pol  xs tree)
    | .imp_left ::xs, .forallE _ tree p _bi            => k? do r.imp_left  p pol tree (visit (!pol) xs tree)
    | .and_left ::xs, regular_and_pattern tree p       => k? do r.and_left  p pol tree (visit   pol  xs tree)
    | .inst     ::xs, .forallE n α b _bi               => k? do r.inst n default α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | [], e => k pol e []
    | xs, e => throwError m! "could not find a subexpression at {xs} in {e}"
  visit pol path tree

-- this is more efficient, as it doesn't require instantiation of the loose bound variables.
def posToPathAndPol : List Nat → Expr → List (TreeBinderKind × Bool) × List Nat :=
  let rec visit (pol : Bool) : List Nat → Expr → List (TreeBinderKind × Bool) × List Nat
    | 1::xs, forall_pattern (body := tree) ..   => Bifunctor.fst (List.cons (.all      , pol)) <| visit   pol  xs tree
    | 1::xs, exists_pattern (body := tree) ..   => Bifunctor.fst (List.cons (.ex       , pol)) <| visit   pol  xs tree
    | 1::xs, imp_pattern _ tree                 => Bifunctor.fst (List.cons (.imp_right, pol)) <| visit   pol  xs tree
    | 1::xs, and_pattern _ tree                 => Bifunctor.fst (List.cons (.and_right, pol)) <| visit   pol  xs tree
    | 0::xs, imp_pattern tree _                 => Bifunctor.fst (List.cons (.imp_left , pol)) <| visit (!pol) xs tree
    | 0::xs, and_pattern tree _                 => Bifunctor.fst (List.cons (.and_left , pol)) <| visit   pol  xs tree
    | 1::xs, instance_pattern (body := tree) .. => Bifunctor.fst (List.cons (.inst     , pol)) <| visit   pol  xs tree
    | xs, _ => ([], xs)
  visit true

def posToPath (pos : List Nat) (tree : Expr) : List (TreeBinderKind) × List Nat :=
  (Bifunctor.fst <| List.map Prod.fst) (posToPathAndPol pos tree)

def posToPath! [Monad m] [MonadError m] (pos : List Nat) (tree : Expr) : m (List (TreeBinderKind)) :=
  match posToPath pos tree with
  | (nodes, []) => return nodes
  | (_, rest) => throwError m!"could not tree-recurse to position {rest} of {pos} in term {tree}"

def findPath : Expr → List TreeBinderKind
  | imp_pattern _ tree                 => .imp_right :: findPath tree
  | and_pattern _ tree                 => .and_right :: findPath tree
  | forall_pattern (body := tree) ..   => .all       :: findPath tree
  | exists_pattern (body := tree) ..   => .ex        :: findPath tree
  | instance_pattern (body := tree) .. => .inst      :: findPath tree
  | _ => []

def findNegativePath : Expr → Option (List TreeBinderKind)
  | imp_pattern _ tree => match findNegativePath tree with
      | some path => .imp_right :: path
      | none => some [.imp_left]
  | and_pattern _ tree                 => (.and_right :: ·) <$> findNegativePath tree
  | forall_pattern (body := tree) ..   => (.all       :: ·) <$> findNegativePath tree
  | exists_pattern (body := tree) ..   => (.ex        :: ·) <$> findNegativePath tree
  | instance_pattern (body := tree) .. => (.inst      :: ·) <$> findNegativePath tree
  | _ => none

def pathToPos (path : List TreeBinderKind) : List Nat :=
  (path.map fun | .imp_left | .and_left => 0 | _ => 1)

def pathPosToPos : List TreeBinderKind → List Nat → List Nat
 | .imp_left::xs
 | .and_left::xs => (0 :: ·) ∘ pathPosToPos xs
 | _::xs => (1 :: ·) ∘ pathPosToPos xs
 | [] => id

def pathPosToTruePos : List TreeBinderKind → List Nat → List Nat
 | .imp_left::xs => (0 :: ·) ∘ pathPosToTruePos xs
 | .and_left::xs => (0 :: 1 :: ·) ∘ pathPosToTruePos xs
 | .ex::xs => (1 :: 1 :: ·) ∘ pathPosToTruePos xs
 | _::xs => (1 :: ·) ∘ pathPosToTruePos xs
 | [] => id

def pathToPol : List TreeBinderKind → Bool
| .imp_left::xs => !pathToPol xs
| _::xs => pathToPol xs
| [] => true

open Meta

partial def makeTreeAux : Expr → MetaM Expr
  | .forallE name domain body bi =>
      withLocalDeclD name domain fun fvar => do
      let body' := (← makeTreeAux (body.instantiate1 fvar)).abstract #[fvar]
      let u ← getLevel domain
      if bi.isInstImplicit
      then
        return mkInstance name u domain body'
      else
        if ← pure !body.hasLooseBVars <&&> isLevelDefEq u .zero 
        then
          return mkImp (← makeTreeAux domain) body'
        else
          return mkForall name u domain body'
            

  | regular_exists_pattern name u domain body _bi =>
      withLocalDeclD name domain fun fvar => do
      let body := body.instantiate1 fvar
      return mkExists name u domain ((← makeTreeAux body).abstract #[fvar])

  | regular_and_pattern p q => return mkAnd (← makeTreeAux p) (← makeTreeAux q)
  | regular_or_pattern  p q => return mkApp2 (.const ``Or  []) (← makeTreeAux p) (← makeTreeAux q)
  | regular_not_pattern p   => return mkApp  (.const ``Not []) (← makeTreeAux p)
  | regular_iff_pattern p q => return mkApp2 (.const ``Iff []) (← makeTreeAux p) (← makeTreeAux q)
  | e@(eq_pattern u α p q) => do
      match ← whnfD α with
      | .sort .zero => return mkApp3 (.const ``Eq [u]) α (← makeTreeAux p) (← makeTreeAux q)
      | _           => pure e
  | and_pattern  p q => return mkApp2 (.const ``And  []) (← makeTreeAux p) (← makeTreeAux q)
  | imp_pattern  p q => return mkApp2 (.const ``Imp  []) (← makeTreeAux p) (← makeTreeAux q)

  | instance_pattern n u d b => withLocalDeclD n d fun fvar =>
    return mkInstance n u d ((← makeTreeAux (b.instantiate1 fvar)).abstract #[fvar])
  | forall_pattern n u d b => withLocalDeclD n d fun fvar =>
    return mkForall n u d ((← makeTreeAux (b.instantiate1 fvar)).abstract #[fvar])
  | exists_pattern n u d b => withLocalDeclD n d fun fvar =>
    return mkExists n u d ((← makeTreeAux (b.instantiate1 fvar)).abstract #[fvar])

  | e => pure e

def makeTree (e : Expr) : MetaM Expr := do
  if ← isDefEq (← inferType e) (.sort .zero) then
    makeTreeAux e
  else
    throwError m! "can't turn {e} : {(← inferType e)} into a tree since it is not a Prop"

open Elab.Tactic

def workOnTreeDefEq (move : Expr → MetaM Expr) : TacticM Unit := do
  replaceMainGoal [← (← getMainGoal).change (← move (← getMainTarget))]
  
def workOnTree (move : Expr → MetaM TreeProof) : TacticM Unit := do
  withMainContext do
    let {newTree, proof} ← move (← getMainTarget)
    match newTree with
    | none =>
      unless ← isTypeCorrect proof do
        throwError m!"closing the goal does not type check{indentExpr proof}"
      (← getMainGoal).assign proof
      replaceMainGoal []

    | some newTree =>
      let mvarNew  ← mkFreshExprSyntheticOpaqueMVar newTree
      let proof  := .app proof mvarNew
      unless ← isTypeCorrect proof do 
        throwError m!"changing the goal does not type check:{indentExpr proof} \nnewTree: {indentExpr newTree}"
      (← getMainGoal).assign proof
      replaceMainGoal [mvarNew.mvarId!]


elab "make_tree" : tactic => workOnTreeDefEq makeTree

syntax treePos := "[" num,* "]"

def getPosition (stx : TSyntax `Tree.treePos) : List Nat :=
  (stx.raw[1].getSepArgs.map (·.isNatLit?.getD 0)).toList

def makeTreePathRec : TreeRecursor MetaM Expr where
  all n _ α _ _ k := withLocalDeclD n α fun fvar => return mkForall n (← getLevel α) α ((← k fvar).abstract #[fvar])
  ex  n u α _ _ k := withLocalDeclD n α fun fvar => return mkExists n u α ((← k fvar).abstract #[fvar])
  imp_right p _ _ k := return mkImp p (← k)
  and_right p _ _ k := return mkAnd p (← k)
  imp_left  p _ _ k := return mkImp (← k) p
  and_left  p _ _ k := return mkAnd (← k) p
  inst n _ α _ _ k := withLocalDeclD n α fun fvar => return mkInstance n (← getLevel α) α ((← k fvar).abstract #[fvar])

def makeTreePath (path : List TreeBinderKind) (tree : Expr) : MetaM Expr :=
  makeTreePathRec.recurseNonTree true tree path (fun _ leaf _ => pure leaf)


def MetaTreeRec : TreeRecursor MetaM α where
  imp_right _ _ _ k := do k
  imp_left  _ _ _ k := do k
  and_right _ _ _ k := do k
  and_left  _ _ _ k := do k

  all  n _ d pol _ k := (if  pol then introFVar else introMVar) n d k
  ex   n _ d pol _ k := (if !pol then introFVar else introMVar) n d k
  inst n _ d _   _ k := (if true then introFVar else introMVar) n d k
where
  introFVar (name : Name) (domain : Expr) (k : Expr → MetaM α) : OptionT MetaM α :=
    withLocalDeclD name domain fun fvar => k fvar
  introMVar (name : Name) (domain : Expr) (k : Expr → MetaM α) : OptionT MetaM α := do
    k (← mkFreshExprMVar domain (userName := name))

def withTreeSubexpr [Inhabited α] (tree : Expr) (pos : List Nat) (k : Bool → Expr → MetaM α) (path : Option (List TreeBinderKind) := none) : MetaM α :=
  let (path, pos) := match path with
    | some path => (path, pos)
    | none => posToPath pos tree
  MetaTreeRec.recurse true tree path fun pol e _path =>
    let rec visit : List Nat → Expr → ReaderT (Array Expr) MetaM α
      | xs   , .mdata _ b       => visit xs b

      | []   , e                => fun fvars => k pol (e.instantiateRev fvars)
      
      | 0::xs, .app f _         => visit xs f
      | 1::xs, .app _ a         => visit xs a

      | 0::xs, .proj _ _ b      => visit xs b

      | 0::xs, .letE _ t _ _ _  => visit xs t
      | 1::xs, .letE _ _ v _ _  => visit xs v
      | 2::xs, .letE n t _ b _  => fun fvars =>
        withLocalDeclD n (t.instantiateRev fvars) fun fvar => visit xs b (fvars.push fvar)
                                                        
      | 0::xs, .lam _ t _ _     => visit xs t
      | 1::xs, .lam n t b _     => fun fvars =>
        withLocalDeclD n (t.instantiateRev fvars) fun fvar => visit xs b (fvars.push fvar)

      | 0::xs, .forallE _ t _ _ => visit xs t
      | 1::xs, .forallE n t b _ => fun fvars =>
        withLocalDeclD n (t.instantiateRev fvars) fun fvar => visit xs b (fvars.push fvar)
      | xs, e                 => throwError m!"could not find subexpression {xs} in '{e}'"

    visit pos e #[]


def TreeProofRec [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] : TreeRecursor m TreeProof where
  imp_right := introProp bindImpRight
  imp_left  := introProp bindImpLeft
  and_right := introProp bindAndRight
  and_left  := introProp bindAndLeft

  all  := introFree bindForall
  ex   := introFree bindExists
  inst := introFree bindInstance
where
  introProp (bind : Expr → Bool → Expr → TreeProof → TreeProof) (p : Expr) (pol : Bool) (tree : Expr) : m TreeProof → OptionT m TreeProof :=
    Functor.map <| some ∘ bind p pol tree

  introFree (bind : Name → Level → Expr → Expr → Bool → Expr → TreeProof → MetaM TreeProof) (name : Name) (u : Level) (domain : Expr) (pol : Bool)
      (tree : Expr) (k : Expr → m TreeProof) : OptionT m TreeProof :=
    withLocalDeclD name domain fun fvar => do
      let treeProof ← k fvar
      bind name u domain fvar pol tree treeProof

def workOnTreeAt (pos : List Nat) (move : List Nat → Bool → Expr → MetaM TreeProof) : TacticM Unit :=
  workOnTree fun tree => do 
    let (path, pos) := posToPath pos tree
    TreeProofRec.recurse true tree path (fun pol tree _path => move pos pol tree)

    
lemma imp (p tree : Prop) (hp : p) : (Imp p tree) → tree := fun h => h hp

def getConstAndTypeFromIdent (id : TSyntax `ident) : MetaM (Expr × Expr) := do
  let name ← Elab.resolveGlobalConstNoOverloadWithInfo id
  let cinfo ← getConstInfo name
  let us ← mkFreshLevelMVarsFor cinfo
  return (.const name us, cinfo.instantiateTypeLevelParams us)

elab "lib_intro" id:ident : tactic =>
  workOnTree fun tree => do
  let (proof, p) ← getConstAndTypeFromIdent id
  let p ← makeTree p
  return {
    newTree := mkApp2 (.const ``Imp []) p tree
    proof := mkApp3 (.const ``imp []) p tree proof
  }
