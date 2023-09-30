import TreeMoves.TreeRewriteDef

namespace Tree

open Lean Meta


def AbstractAux (depth : Nat) : Pos → Expr → MetaM (Expr × Expr)
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



lemma give_name (p : α → Prop) (a : α) : p a ↔ Forall α fun b => Imp (a = b) (p b) :=
  ⟨fun h _ g => g.rec h, fun h => h a rfl⟩









def betaAbstractAux (pos : Pos) (e : Expr) : MetaM Expr := do
  let (b, v) ← AbstractAux 0 pos e
  if v.hasLooseBVars then throwError m! "cannot β-abstract a subexpression with loose bound variables: {v}"
  return .app (.lam `x (← inferType v) b .default) v

def letAbstractAux (pos : Pos) (e : Expr) : MetaM Expr := do
  let (b, v) ← AbstractAux 0 pos e
  if v.hasLooseBVars then throwError m! "cannot let-abstract a subexpression with loose bound variables: {v}"
  return mkLet `x (← inferType v) v b

def betaAbstract (pos abstractPos : Pos) (_tree : Expr) : MetaM (Option String) := do
  let rec takePrefix {α : Type} [BEq α] : List α → List α → Option (List α)
    | [], xs => some xs
    | _ , [] => none
    | x::xs, y::ys => if x == y then takePrefix xs ys else none
  let some pos' := takePrefix pos abstractPos | return none
  return s! "beta_abstract {pos} {pos'}"

elab "beta_abstract" pos:treePos pos':treePos : tactic => do
  let pos := getPosition pos
  let pos' := getPosition pos'
  workOnTreeDefEq (edit pos (betaAbstractAux pos'))

example : (fun x => x) 1 = 1 := by
  beta_abstract [1] []
  rfl
