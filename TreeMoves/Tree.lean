import TreeMoves.TreeLemmas

namespace Tree

open Lean

/- These are the match patterns for the Tree nodes -/
@[match_pattern] def not_pattern (p : Expr) : Expr := mkApp (.const ``Not []) p

@[match_pattern] def imp_pattern (p q : Expr) : Expr := mkApp2 (.const ``Imp []) p q
@[match_pattern] def and_pattern (p q : Expr) : Expr := mkApp2 (.const ``And []) p q

@[match_pattern]
def forall_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (body : Expr) {bi : BinderInfo} : Expr :=
  mkApp2 (.const ``Forall [u]) domain' (.lam name domain body bi)
@[match_pattern]
def exists_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (body : Expr) {bi : BinderInfo} : Expr :=
  mkApp2 (.const ``Exists [u]) domain' (.lam name domain body bi)

@[match_pattern]
def instance_pattern (name : Name) (u : Level) (cls : Expr) {cls' : Expr} (body : Expr) {bi : BinderInfo} : Expr :=
  mkApp2 (.const ``Instance [u]) cls' (.lam name cls body bi)

/- These are match patterns for some regular Lean logical combinators -/
@[match_pattern] def regular_not_pattern (p : Expr) : Expr :=        mkApp  (.const `Not []) p
@[match_pattern] def regular_and_pattern (p q : Expr) : Expr :=      mkApp2 (.const `And []) p q
@[match_pattern] def regular_iff_pattern (p q : Expr) : Expr :=      mkApp2 (.const `Iff []) p q
@[match_pattern] def eq_pattern (u : Level) (α p q : Expr) : Expr := mkApp3 (.const `Eq [u]) α p q
@[match_pattern] def regular_or_pattern (p q : Expr) : Expr :=       mkApp2 (.const `Or  []) p q
@[match_pattern]
def regular_exists_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (body : Expr) (bi : BinderInfo) : Expr :=
  mkApp2 (.const `Exists [u]) domain' (.lam name domain body bi)

/-- Return True if the expression starts with a Tree node. -/
def isTree : Expr → Bool
| imp_pattern ..
| and_pattern ..
| not_pattern ..
| forall_pattern ..
| exists_pattern ..
| instance_pattern .. => true
| _ => false

abbrev Pos := List ℕ
abbrev TreePos := List ℕ

def badPosMessage (e : Expr) (pos : Pos) : MessageData := m! "could not find position {pos} in target {e}"
def badTreePosMessage (e : Expr) (pos : TreePos) : MessageData := m! "could not find tree position {pos} in target {e}"

/-- The general structure for recursing through a Tree expression. -/
structure DirectTreeRecursor (α : Type u) where
  all (name : Name) (u : Level) (domain : Expr) : Bool → Expr → α → α
  ex  (name : Name) (u : Level) (domain : Expr) : Bool → Expr → α → α
  inst (n : Name) (u : Level) (cls : Expr) : Bool → Expr → α → α

  imp_right (p : Expr) : Bool → Expr → α → α
  and_right (p : Expr) : Bool → Expr → α → α
  imp_left  (p : Expr) : Bool → Expr → α → α
  and_left  (p : Expr) : Bool → Expr → α → α
  not : Bool → Expr → α → α 

def DirectTreeRecursor.recurse [Monad m] [MonadError m] (r : DirectTreeRecursor (m α)) (pol : Bool) (tree : Expr) (pos : TreePos)
  (k : Bool → Expr → m α) : m α :=
  let rec visit (pol : Bool) (ys : TreePos) (e : Expr) : m α :=
    match ys, e with
    | 1::xs, forall_pattern   n u α b => r.all  n u α pol (.lam n α b .default) (visit pol xs b)
    | 1::xs, exists_pattern   n u α b => r.ex   n u α pol (.lam n α b .default) (visit pol xs b)
    | 1::xs, instance_pattern n u α b => r.inst n u α pol (.lam n α b .default) (visit pol xs b)
    | 1::xs, imp_pattern p tree     => r.imp_right p pol tree (visit   pol  xs tree)
    | 1::xs, and_pattern p tree     => r.and_right p pol tree (visit   pol  xs tree)
    | 0::xs, imp_pattern tree p     => r.imp_left  p pol tree (visit (!pol) xs tree)
    | 0::xs, and_pattern tree p     => r.and_left  p pol tree (visit   pol  xs tree)
    | [], e => k pol e
    | xs, e => throwError badTreePosMessage e xs
  visit pol pos tree


/-- The default/empty TreeRecursor. This is usefull for extracting a subexpression or the polarity of a subexpression. -/
def emptyRecursor : DirectTreeRecursor α where
    all  _ _ _ _ _ k := k
    ex   _ _ _ _ _ k := k
    inst _ _ _ _ _ k := k
    imp_left  _ _ _ k := k
    imp_right _ _ _ k := k
    and_left  _ _ _ k := k
    and_right _ _ _ k := k
    not _ _ k := k

def getPolarity [Monad m] [MonadError m] (tree : Expr) (pos : TreePos) : m Bool :=
  emptyRecursor.recurse true tree pos (fun pol _ => return pol)

def getExpression [Monad m] [MonadError m] (tree : Expr) (pos : TreePos) : m Expr :=
  emptyRecursor.recurse true tree pos (fun _ e => return e )



structure TreeRecursor (m : Type u → Type v) (α : Type u) where
  all (name : Name) (u : Level) (domain : Expr) : Bool → Expr → (Expr → m α) → OptionT m α
  ex  (name : Name) (u : Level) (domain : Expr) : Bool → Expr → (Expr → m α) → OptionT m α
  inst (n : Name) (u : Level) (cls : Expr) : Bool → Expr → (Expr → m α) → OptionT m α

  imp_right (p : Expr) : Bool → Expr → m α → OptionT m α
  and_right (p : Expr) : Bool → Expr → m α → OptionT m α
  imp_left  (p : Expr) : Bool → Expr → m α → OptionT m α
  and_left  (p : Expr) : Bool → Expr → m α → OptionT m α
  not : Bool → Expr → m α → OptionT m α


partial def TreeRecursor.recurse [Inhabited α] [Monad m] [MonadError m] (r : TreeRecursor m α) (pol : Bool) (tree : Expr) (pos : TreePos)
  (k : Bool → Expr → TreePos → m α) : m α :=
  let rec visit [Inhabited α] (pol : Bool) (ys : TreePos) (e : Expr) : m α :=
    let k? l := do (Option.getDM (← l) (k pol e ys))
    match ys, e with
    | 1::xs, forall_pattern   n u α b => k? do r.all  n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | 1::xs, exists_pattern   n u α b => k? do r.ex   n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | 1::xs, instance_pattern n u α b => k? do r.inst n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | 1::xs, imp_pattern p tree       => k? do r.imp_right p pol tree (visit   pol  xs tree)
    | 1::xs, and_pattern p tree       => k? do r.and_right p pol tree (visit   pol  xs tree)
    | 0::xs, imp_pattern tree p       => k? do r.imp_left  p pol tree (visit (!pol) xs tree)
    | 0::xs, and_pattern tree p       => k? do r.and_left  p pol tree (visit   pol  xs tree)
    | 1::xs, not_pattern tree         => k? do r.not         pol tree (visit (!pol) xs tree)
    | [], e => k pol e []
    | xs, e => throwError badTreePosMessage e xs
  visit pol pos tree

open Meta
/-- If the expression is an `Expr.forallE`, replace it by a `Tree.Forall`, `Tree.Instance` or `Tree.Imp` node as appropriate.-/
def replaceForallE : Expr → MetaM Expr
  | .forallE name domain body bi => do
    let u ← getLevel domain
    return if bi.isInstImplicit
      then mkInstance name u domain body
      else if ← pure !body.hasLooseBVars <&&> isLevelDefEq u .zero
        then mkImp domain body
        else mkForall name u domain body
  | e => return e

partial def TreeRecursor.recurseNonTree [Inhabited α] (r : TreeRecursor MetaM α)
  (pol : Bool) (tree : Expr) (path : TreePos) (k : Bool → Expr → TreePos → MetaM α) : MetaM α :=
  let rec visit [Inhabited α] (pol : Bool) (ys : TreePos) (e : Expr) : MetaM α :=
    let k? l := do (Option.getDM (← l) (k pol e ys))
    do match ys, (← replaceForallE e) with
    | 1::xs, forall_pattern n u α b           => k? do r.all  n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | 1::xs, regular_exists_pattern n u α b _ => k? do r.ex   n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | 1::xs, instance_pattern n u α b         => k? do r.inst n u α pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | 1::xs, imp_pattern p tree               => k? do r.imp_right p pol tree (visit   pol  xs tree)
    | 1::xs, regular_and_pattern p tree       => k? do r.and_right p pol tree (visit   pol  xs tree)
    | 0::xs, imp_pattern tree p               => k? do r.imp_left  p pol tree (visit (!pol) xs tree)
    | 0::xs, regular_and_pattern tree p       => k? do r.and_left  p pol tree (visit   pol  xs tree)
    | 1::xs, regular_not_pattern tree         => k? do r.not         pol tree (visit (!pol) xs tree)
    | [], e => k pol e []    
    | xs, e => throwError badTreePosMessage e xs
  visit pol path tree


def findTreePos : Expr → TreePos
  | imp_pattern _ tree                 => 1 :: findTreePos tree
  | and_pattern _ tree                 => 1 :: findTreePos tree
  | forall_pattern (body := tree) ..   => 1 :: findTreePos tree
  | exists_pattern (body := tree) ..   => 1 :: findTreePos tree
  | instance_pattern (body := tree) .. => 1 :: findTreePos tree
  | _ => []

def findNegativeTreePos : Expr → Option TreePos
  | imp_pattern _ tree => match findNegativeTreePos tree with
      | some path => 1 :: path
      | none => some [0]
  | and_pattern _ tree                 => (1 :: ·) <$> findNegativeTreePos tree
  | forall_pattern (body := tree) ..   => (1 :: ·) <$> findNegativeTreePos tree
  | exists_pattern (body := tree) ..   => (1 :: ·) <$> findNegativeTreePos tree
  | instance_pattern (body := tree) .. => (1 :: ·) <$> findNegativeTreePos tree
  | _ => none

partial def makeTreeAux (e : Expr) : MetaM Expr := do match ← replaceForallE e with
  | regular_exists_pattern name u domain body _bi =>
      withLocalDeclD name domain fun fvar => do
      let body ← makeTreeAux (body.instantiate1 fvar)
      return mkExists name u domain ((body).abstract #[fvar])

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
  /- by doing this isDefEq check, the expression is forced to be a proposition, as it might have been universe polymorphic -/
  if ← isDefEq (← inferType e) (.sort .zero) then
    makeTreeAux e
  else
    throwError m! "can't turn {e} : {(← inferType e)} into a tree since it is not a Prop"

open Elab.Tactic

def workOnTreeDefEq (move : Expr → MetaM Expr) : TacticM Unit := do
  replaceMainGoal [← (← getMainGoal).change (← makeTree (← move (← getMainTarget)))] 
  
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
      let mvarNew  ← mkFreshExprSyntheticOpaqueMVar (← makeTree newTree)
      let proof  := .app proof mvarNew
      unless ← isTypeCorrect proof do 
        throwError m!"changing the goal does not type check:{indentExpr proof} \nnewTree: {indentExpr newTree}"
      (← getMainGoal).assign proof
      replaceMainGoal [mvarNew.mvarId!]


elab "make_tree" : tactic => workOnTreeDefEq pure

syntax treePos := "[" num,* "]"

def splitPosition (pos : List ℕ) : TreePos × Pos :=
  splitAt2 pos
where
  splitAt2 : List ℕ → TreePos × Pos
  | x::xs => if x == 2 then ([], xs) else Bifunctor.fst (x::·) $ splitAt2 xs
  | [] => ([],[])

def printPosition (treePos : TreePos) (pos : Pos) : String :=
  if pos == [] then s! "{treePos}"
  else s! "{treePos ++ 2 :: pos}" 
    

def getPosition (stx : TSyntax `Tree.treePos) : List ℕ :=
  (stx.raw[1].getSepArgs.map (·.isNatLit?.getD 0)).toList

def getSplitPosition (stx : TSyntax `Tree.treePos) : TreePos × Pos := splitPosition (getPosition stx)

def makeTreePathRec : TreeRecursor MetaM Expr where
  all n u α _ _ k := withLocalDeclD n α fun fvar => return mkForall n u α ((← k fvar).abstract #[fvar])
  ex  n u α _ _ k := withLocalDeclD n α fun fvar => return mkExists n u α ((← k fvar).abstract #[fvar])
  inst n u α _ _ k := withLocalDeclD n α fun fvar => return mkInstance n u α ((← k fvar).abstract #[fvar])

  imp_right p _ _ k := return mkImp p (← k)
  and_right p _ _ k := return mkAnd p (← k)
  imp_left  p _ _ k := return mkImp (← k) p
  and_left  p _ _ k := return mkAnd (← k) p
  not _ _ k         := return mkNot (← k)

def makeTreePath (pos : TreePos) (tree : Expr) : MetaM Expr :=
  makeTreePathRec.recurseNonTree true tree pos (fun _ leaf _ => pure leaf)


def MetaTreeRec : TreeRecursor MetaM α where
  imp_right _ _ _ k := do k
  imp_left  _ _ _ k := do k
  and_right _ _ _ k := do k
  and_left  _ _ _ k := do k
  not         _ _ k := do k

  all  n _ d pol _ k := (if  pol then introFVar else introMVar) n d k
  ex   n _ d pol _ k := (if !pol then introFVar else introMVar) n d k
  inst n _ d _   _ k := (if true then introFVar else introMVar) n d k
where
  introFVar (name : Name) (domain : Expr) (k : Expr → MetaM α) : OptionT MetaM α :=
    withLocalDeclD name domain fun fvar => k fvar
  introMVar (name : Name) (domain : Expr) (k : Expr → MetaM α) : OptionT MetaM α := do
    k (← mkFreshExprMVar domain (userName := name))

def withTreeSubexpr [Inhabited α] (tree : Expr) (treePos : TreePos) (pos : Pos) (k : Bool → Expr → MetaM α) : MetaM α :=
  MetaTreeRec.recurse true tree treePos fun pol e _ =>
    let rec visit : Pos → Expr → ReaderT (Array Expr) MetaM α
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
      | xs, e                 => throwError badPosMessage e xs

    visit pos e #[]


def TreeProofRec [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] (saveClosed : Bool) : TreeRecursor m TreeProof where
  imp_right := introProp bindImpRight
  imp_left  := introProp bindImpLeft
  and_right := introProp bindAndRight
  and_left  := introProp bindAndLeft
  not pol tree k := bindNot pol tree <$> k

  all  := introFree bindForall
  ex   := introFree bindExists
  inst := introFree bindInstance
where
  introProp (bind : Bool → Expr → Bool → Expr → TreeProof → TreeProof) (p : Expr) (pol : Bool) (tree : Expr) (k : m TreeProof) : OptionT m TreeProof :=
    bind saveClosed p pol tree <$> k

  introFree (bind : Name → Level → Expr → Expr → Bool → Expr → TreeProof → MetaM TreeProof) (name : Name) (u : Level) (domain : Expr) (pol : Bool)
      (tree : Expr) (k : Expr → m TreeProof) : OptionT m TreeProof :=
    withLocalDeclD name domain fun fvar => do
      let treeProof ← k fvar
      bind name u domain fvar pol tree treeProof

def workOnTreeAt (pos : TreePos) (move : Bool → Expr → MetaM TreeProof) (saveClosed : Bool := false) : TacticM Unit :=
  workOnTree fun tree => do 
    (TreeProofRec saveClosed).recurse true tree pos (fun pol tree _ => move pol tree)

    
lemma imp (p tree : Prop) (hp : p) : (Imp p tree) → tree := fun h => h hp

open Elab in
/-- if this is an ident, return the name, and add the info to the infotree.
This means that if you hover over the name, you will see the type information of the constant. -/
def getIdWithInfo [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m]
    (id : Syntax) (expectedType? : Option Expr := none) : m Name := do
  let n := id.getId
  if (← getInfoState).enabled then
    addConstInfo id n expectedType?
  return n

def getConstAndTypeFromIdent (id : TSyntax `ident) : MetaM (Expr × Expr) := do
  let name ← getIdWithInfo id
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
