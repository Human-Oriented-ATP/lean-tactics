import MotivatedMoves.Moves.TreeRewriteDef

namespace Tree

open Lean Meta

/-- The type used for binding an abstraction as close to the root as possible,
while requiring that the abstracted subexpression contains no loose bound variables.
The `outer` expression is the original expression with the inner expression replaced by `abstractedExpression`. -/
inductive ExprAbstraction where
  | abstract (outer : Expr) (inner : Expr) : ExprAbstraction
  | closed : Expr → ExprAbstraction

def abstractedExpression : Expr := .fvar ⟨`abstracted_expression⟩

def mkLetAbstraction (name : Name) (outer : Expr) (inner : Expr) : MetaM Expr := do
  let outer := outer.abstract #[abstractedExpression]
  return mkLet name (← inferType inner) inner outer

partial def AbstractExpr (name : Name) : InnerPosition → Expr → MetaM ExprAbstraction
  | xs   , .mdata d b        => return wrap (.mdata d ·) (← AbstractExpr name xs b)

  | 0::xs, .app f a          => return wrap (.app · a) (← AbstractExpr name xs f)
  | 1::xs, .app f a          => return wrap (.app f ·) (← AbstractExpr name xs a)

  | 0::xs, .proj n i b       => return wrap (.proj n i ·) (← AbstractExpr name xs b)

  | 0::xs, .letE n t v b d   => return wrap (.letE n · v b d) (← AbstractExpr name xs t)
  | 1::xs, .letE n t v b d   => return wrap (.letE n t · b d) (← AbstractExpr name xs v)
  | 2::xs, .letE n t v b d   => return wrap (.letE n t v · d) (← withVar n t b xs)

  | 0::xs, .lam n t b bi     => return wrap (.lam n · b bi) (← AbstractExpr name xs t)
  | 1::xs, .lam n t b bi     => return wrap (.lam n t · bi) (← withVar n t b xs)

  | 0::xs, .forallE n t b bi => return wrap (.forallE n · b bi) (← AbstractExpr name xs t)
  | 1::xs, .forallE n t b bi => return wrap (.forallE n t · bi) (← withVar n t b xs)

  | [], e                    => return .abstract abstractedExpression e
  | xs, e                    => throwError badInnerPositionMessage e xs
where
  wrap (wrap : Expr → Expr) : ExprAbstraction → ExprAbstraction
    | .abstract outer inner => .abstract (wrap outer) inner
    | .closed e => .closed (wrap e)

  withVar (n : Name) (domain body : Expr) (pos : InnerPosition) : MetaM ExprAbstraction := do
    withLocalDeclD n domain fun fvar => do
    match ← AbstractExpr n pos (body.instantiate1 fvar) with
      | .abstract outer inner => do
        if (inner.abstract #[fvar]).hasLooseBVars then
          let result ← mkLetAbstraction name outer inner
          return .closed (result.abstract #[fvar])
        else
          let outer := outer.abstract #[fvar]
          return .abstract outer inner

      | .closed e =>
        return .closed (e.abstract #[fvar])



lemma give_name (p : α → Prop) (a : α) : Forall α (fun b => Imp (a = b) (p b)) → p a :=
  fun h => h a rfl

lemma give_name' (p : α → Prop) (a : α) : p a → Exists α (fun b => And (a = b) (p b)) :=
  fun h => ⟨a, rfl, h⟩

lemma give_meta_name (p : α → Prop) (a : α) : Exists α (fun b => And (a = b) (p b)) → p a :=
  fun ⟨_, heq, h⟩ => heq ▸ h

lemma give_meta_name' (p : α → Prop) (a : α) : p a → Forall α (fun b => Imp (a = b) (p b)) :=
  fun h _ heq => heq ▸ h

/-- Similar to ExprAbstraction, but for trees -/
inductive Abstraction where
  | abstract (outer : Expr) (inner : Expr) : Abstraction
  | closed : TreeProof → Abstraction
deriving Inhabited

def mkNameAbstraction (meta : Bool) (name : Name) (outer : Expr) (inner : Expr) (pol : Bool) : MetaM TreeProof := do
  let outer := outer.abstract #[abstractedExpression]
  let type ← inferType inner
  let u ← getLevel type
  return if meta
  then if pol
    then {
      newTree := mkExists name u type (mkAnd (mkApp3 (.const ``Eq [u]) type inner (.bvar 0)) outer)
      proof := mkApp3 (.const ``give_meta_name  [u]) type (.lam name type outer .default) inner }
    else {
      newTree := mkForall name u type (mkImp (mkApp3 (.const ``Eq [u]) type inner (.bvar 0)) outer)
      proof := mkApp3 (.const ``give_meta_name' [u]) type (.lam name type outer .default) inner }

  else if pol
    then {
      newTree := mkForall name u type (mkImp (mkApp3 (.const ``Eq [u]) type inner (.bvar 0)) outer)
      proof := mkApp3 (.const ``give_name  [u]) type (.lam name type outer .default) inner }
    else {
      newTree := mkExists name u type (mkAnd (mkApp3 (.const ``Eq [u]) type inner (.bvar 0)) outer)
      proof := mkApp3 (.const ``give_name' [u]) type (.lam name type outer .default) inner }


def NamingRecursor (meta : Bool) (name : Name) : TreeRecursor MetaM Abstraction where
  imp_right p := introProp (bindImpRight false p) (mkImp p)
  imp_left  p := introProp (bindImpLeft  false p) (mkImp · p)
  and_right p := introProp (bindAndRight false p) (mkAnd p)
  and_left  p := introProp (bindAndLeft  false p) (mkAnd · p)
  not         := introProp bindNot mkNot

  all  := introFree bindForall mkForall
  ex   := introFree bindExists mkExists
  inst := introFree bindInstance mkInstance
where
  introProp (bind : Bool → Expr → TreeProof → TreeProof) (wrap : Expr → Expr) (pol : Bool) (tree : Expr) (k : MetaM Abstraction) : OptionT MetaM Abstraction := do
    match ← k with
    | .abstract outer inner => return .abstract (wrap outer) inner
    | .closed treeProof => return .closed $ bind pol tree treeProof

  introFree (bind : Name → Level → Expr → Expr → Bool → Expr → TreeProof → MetaM TreeProof) (wrap : Name → Level → Expr → Expr → Expr) (n : Name) (u : Level) (domain : Expr) (pol : Bool)
      (tree : Expr) (k : Expr → MetaM Abstraction) : OptionT MetaM Abstraction :=
    withLocalDeclD n domain fun fvar => do
    match ← k fvar with
    | .abstract outer inner => do
      if (inner.abstract #[fvar]).hasLooseBVars then
        let treeProof ← mkNameAbstraction meta name outer inner pol
        let treeProof ← bind n u domain fvar pol tree treeProof
        return .closed treeProof
      else
        let outer := outer.abstract #[fvar]
        return .abstract (wrap n u domain outer) inner

    | .closed treeProof => do
      let treeProof ← bind n u domain fvar pol tree treeProof
      return .closed treeProof


def NameSubExpr (meta : Bool) (name : Name) (treePos : OuterPosition) (pos : InnerPosition) (tree : Expr) : MetaM TreeProof := do
  let result ← (NamingRecursor meta name).recurse true tree treePos fun _pol e _ => do
    match ← AbstractExpr name pos e with
    | .abstract outer inner => return .abstract outer inner
    | .closed eNew => return .closed { newTree := eNew, proof := .lam `_h e (.bvar 0) .default }

  match result with
    | .abstract outer inner => do
        let treeProof ← mkNameAbstraction meta name outer inner true
        return treeProof
    | .closed treeProof => do
      return treeProof


elab "tree_name" name:ident pos:treePos : tactic => do
  let (treePos, pos) := getOuterInnerPosition pos
  let name := name.getId
  workOnTree $ NameSubExpr false name treePos pos

elab "tree_name_meta" name:ident pos:treePos : tactic => do
  let (treePos, pos) := getOuterInnerPosition pos
  let name := name.getId
  workOnTree $ NameSubExpr true name treePos pos

-- example : ∃ f : ℕ → ℕ, ∀ w, f (w + 1) = w := by
--   make_tree
--   tree_name_meta xx [1,1,2,0,1,1]

/- As you can see, if the names expression contains a locally bound variable,
we get a let expression from the naming move. -/
-- example : {1} = {n | n = 1} := by
--   make_tree
--   tree_name h [2,1,1,1]

def AbstractAux (depth : ℕ) : InnerPosition → Expr → MetaM (Expr × Expr)
  | xs   , .mdata d b        => return Bifunctor.fst (.mdata d ·) (← AbstractAux depth xs b)

  | 0::xs, .app f a          => return Bifunctor.fst (.app · a) (← AbstractAux depth xs f)
  | 1::xs, .app f a          => return Bifunctor.fst (.app f ·) (← AbstractAux depth xs a)

  | 0::xs, .proj n i b       => return Bifunctor.fst (.proj n i ·) (← AbstractAux depth xs b)

  | 0::xs, .letE n t v b d   => return Bifunctor.fst (.letE n · v b d) (← AbstractAux depth xs t)
  | 1::xs, .letE n t v b d   => return Bifunctor.fst (.letE n t · b d) (← AbstractAux depth xs v)
  | 2::xs, .letE n t v b d   => return Bifunctor.fst (.letE n t v · d) (← AbstractAux (depth+1) xs b)

  | 0::xs, .lam n t b bi     => return Bifunctor.fst (.lam n · b bi) (← AbstractAux depth xs t)
  | 1::xs, .lam n t b bi     => return Bifunctor.fst (.lam n t · bi) (← AbstractAux (depth+1) xs b)

  | 0::xs, .forallE n t b bi => return Bifunctor.fst (.forallE n · b bi) (← AbstractAux depth xs t)
  | 1::xs, .forallE n t b bi => return Bifunctor.fst (.forallE n t · bi) (← AbstractAux (depth+1) xs b)

  | []   , e                 => return (.bvar depth, e)
  | list , e                 => throwError m!"could not find subexpression {list} in '{e}'"




def betaAbstractAux (pos : InnerPosition) (e : Expr) : MetaM Expr := do
  let (b, v) ← AbstractAux 0 pos e
  if v.hasLooseBVars then throwError m! "cannot β-abstract a subexpression with loose bound variables: {v}"
  return .app (.lam `x (← inferType v) b .default) v

-- def letAbstractAux (pos : InnerPosition) (e : Expr) : MetaM Expr := do
--   let (b, v) ← AbstractAux 0 pos e
--   if v.hasLooseBVars then throwError m! "cannot let-abstract a subexpression with loose bound variables: {v}"
--   return mkLet `x (← inferType v) v b

def betaAbstract (pos abstractPos : InnerPosition) (_tree : Expr) : MetaM (Option String) := do
  let rec takePrefix {α : Type} [BEq α] : List α → List α → Option (List α)
    | [], xs => some xs
    | _ , [] => none
    | x::xs, y::ys => if x == y then takePrefix xs ys else none
  let some pos' := takePrefix pos abstractPos | return none
  return s! "beta_abstract {pos} {pos'}"

elab "beta_abstract" pos:treePos pos':treePos : tactic => do
  let (treePos, pos) := getOuterInnerPosition pos
  let pos' := getPosition pos'
  workOnTreeDefEq (edit treePos pos (betaAbstractAux pos'))

example : (fun x => x) 1 = 1 := by
  beta_abstract [2,1] []
  rfl
