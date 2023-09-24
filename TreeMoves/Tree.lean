import TreeMoves.TreeLemmas

namespace Tree

open Lean

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


structure Recursor (α : Type u) where
  all (name : Name) (u : Level) (domain : Expr) : Bool → Expr → (Expr → α) → α
  ex  (name : Name) (u : Level) (domain : Expr) : Bool → Expr → (Expr → α) → α

  imp_right (p : Expr) : Bool → Expr → α → α
  and_right (p : Expr) : Bool → Expr → α → α
  imp_left  (p : Expr) : Bool → Expr → α → α
  and_left  (p : Expr) : Bool → Expr → α → α

  inst (n : Name) (u : Level) (cls : Expr) : Bool → Expr → (Expr → α) → α

structure OptionRecursor (m : Type u → Type v) (α : Type u) where
  all (name : Name) (u : Level) (domain : Expr) : Bool → Expr → (Expr → m α) → OptionT m α
  ex  (name : Name) (u : Level) (domain : Expr) : Bool → Expr → (Expr → m α) → OptionT m α

  imp_right (p : Expr) : Bool → Expr → m α → OptionT m α
  and_right (p : Expr) : Bool → Expr → m α → OptionT m α
  imp_left  (p : Expr) : Bool → Expr → m α → OptionT m α
  and_left  (p : Expr) : Bool → Expr → m α → OptionT m α

  inst (n : Name) (u : Level) (cls : Expr) : Bool → Expr → (Expr → m α) → OptionT m α

instance [Monad m] [MonadNameGenerator m] : EmptyCollection (OptionRecursor m α) where
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

-- partial def Recursor.recurseM [Inhabited α] [Monad m] [MonadError m] (r : Recursor (m α)) (pol : Bool) (tree : Expr) (pos : List TreeBinderKind) (k : Bool → Expr → m α) : m α :=
--   let rec visit [Inhabited α] (pol : Bool) : List TreeBinderKind → Expr → m α  
--     | .all      ::xs, forall_pattern n u α b => r.all n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
--     | .ex       ::xs, exists_pattern n u α b => r.ex  n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
--     | .imp_right::xs, imp_pattern p tree     => r.imp_right p pol tree (visit   pol  xs tree)
--     | .and_right::xs, and_pattern p tree     => r.and_right p pol tree (visit   pol  xs tree)
--     | .imp_left ::xs, imp_pattern tree p     => r.imp_left  p pol tree (visit (!pol) xs tree)
--     | .and_left ::xs, and_pattern tree p     => r.and_left  p pol tree (visit   pol  xs tree)
--     | .inst     ::xs, instance_pattern n u α b => r.inst n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
--     | [], e => k pol e
--     | xs, e => throwError m!"could not tree-recurse to position {xs} in term {e}"
--   visit pol pos tree

partial def OptionRecursor.recurse [Inhabited α] [Monad m] [MonadError m] (r : OptionRecursor m α) (pol : Bool := true) (tree : Expr) (path : List TreeBinderKind)
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

partial def OptionRecursor.recurseNonTree [Inhabited α] [Monad m] [MonadError m] (r : OptionRecursor m α) (pol : Bool := true) (tree : Expr) (path : List TreeBinderKind)
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
        return mkApp2 (.const ``Instance [u]) domain (.lam name domain body' .default)
      else
        if ← pure !body.hasLooseBVars <&&> isLevelDefEq u .zero 
        then
          return mkApp2 (.const ``Imp []) (← makeTreeAux domain) body'
        else
          return mkApp2 (.const ``Forall [u]) domain (.lam name domain body' .default)
            

  | regular_exists_pattern name u domain body _bi =>
      withLocalDeclD name domain fun fvar => do
      let body := body.instantiate1 fvar
      return mkApp2 (.const ``Exists [u]) domain (.lam name domain ((← makeTreeAux body).abstract #[fvar]) .default)

  | regular_and_pattern p q => return mkApp2 (.const ``And []) (← makeTreeAux p) (← makeTreeAux q)
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
    return mkApp2 (.const ``Instance [u]) d (.lam n d ((← makeTreeAux (b.instantiate1 fvar)).abstract #[fvar]) .default)
  | forall_pattern n u d b => withLocalDeclD n d fun fvar =>
    return mkApp2 (.const ``Forall [u]) d (.lam n d ((← makeTreeAux (b.instantiate1 fvar)).abstract #[fvar]) .default)
  | exists_pattern n u d b => withLocalDeclD n d fun fvar =>
    return mkApp2 (.const ``Exists [u]) d (.lam n d ((← makeTreeAux (b.instantiate1 fvar)).abstract #[fvar]) .default)

  | e => pure e

def makeTree (e : Expr) : MetaM Expr := do
  if ← isDefEq (← inferType e) (.sort .zero) then
    makeTreeAux e
  else
    throwError m! "can't turn {e} : {(← inferType e)} into a tree since it is not a Prop"

open Elab Tactic

elab "make_tree" : tactic => do
  replaceMainGoal [← (← getMainGoal).change (← makeTree (← getMainTarget))]

syntax treePos := "[" num,* "]"

def getPosition (stx : Syntax) : List Nat :=
  (stx[1].getSepArgs.map (·.isNatLit?.getD 0)).toList

def makeTreePathRec : OptionRecursor MetaM Expr where
  all n _ α _ _ k := withLocalDeclD n α fun fvar => return mkApp2 (.const ``Forall [← getLevel α]) α (.lam n α ((← k fvar).abstract #[fvar]) .default)
  ex  n u α _ _ k := withLocalDeclD n α fun fvar => return mkApp2 (.const ``Exists [u]) α (.lam n α ((← k fvar).abstract #[fvar]) .default)
  imp_right p _ _ k := return mkApp2 (.const ``Imp []) p (← k)
  and_right p _ _ k := return mkApp2 (.const ``And []) p (← k)
  imp_left  p _ _ k := return mkApp2 (.const ``Imp []) (← k) p
  and_left  p _ _ k := return mkApp2 (.const ``And []) (← k) p
  inst n _ α _ _ k := withLocalDeclD n α fun fvar => return mkApp2 (.const ``Instance [← getLevel α]) α (.lam n α ((← k fvar).abstract #[fvar]) .default)

def makeTreePath (path : List TreeBinderKind) (tree : Expr) : MetaM Expr :=
  makeTreePathRec.recurseNonTree true tree path (fun _ leaf _ => pure leaf)


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


def TreeRec [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] : OptionRecursor m TreeProof where
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
    TreeRec.recurse true tree path (fun pol tree _path => move pos pol tree)

    
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
