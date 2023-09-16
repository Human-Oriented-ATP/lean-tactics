import TreeRewrite

namespace Tree

open Lean Elab Tactic Meta


def normalize (fvars : Array Expr) (conv : Syntax) (lhs : Expr) : TermElabM RewriteInfo := do
  let lhs := lhs.instantiateRev fvars

  let (rhs, proof) ← Conv.mkConvGoalFor lhs
  let MVarIds ← Elab.Tactic.run proof.mvarId! do evalTactic conv
  for mvarId in MVarIds do
    liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
  
  let rhs ← instantiateMVars rhs
  let proof ← instantiateMVars proof
  let lctx ← getLCtx

  let n := fvars.size
  let motive_core := n.fold (.bvar · |> mkApp ·) (.bvar n)

  let proof ← fvars.foldrM (fun fvar proof => mkAppM ``funext #[lctx.mkLambda #[fvar] proof]) proof
  let type := lctx.mkForall fvars (← inferType rhs)
  let rhs := rhs.abstract fvars

  return (motive_core, rhs, proof, type)


private def recurseToPosition (target : Expr) (conv : Syntax) (pos : List Nat) : TermElabM RewriteInfo :=
  
  let rec visit (fvars : Array Expr) : List Nat → Expr → TermElabM RewriteInfo
    | xs   , .mdata d b        => do let (e, e', z) ← visit fvars xs b; return (.mdata d e, .mdata d e', z)

    | []   , e                 => normalize fvars conv e
    
    | 0::xs, .app f a          => do let (e, e', z) ← visit fvars xs f; return (.app e a, .app e' a, z)
    | 1::xs, .app f a          => do let (e, e', z) ← visit fvars xs a; return (.app f e, .app f e', z)

    | 0::xs, .proj n i b       => do let (e, e', z) ← visit fvars xs b; return (.proj n i e, .proj n i e', z)

    | 0::xs, .letE n t v b d   => do let (e, e', z) ← visit fvars xs t; return (.letE n e v b d, .letE n e' v b d, z)
    | 1::xs, .letE n t v b d   => do let (e, e', z) ← visit fvars xs v; return (.letE n t e b d, .letE n t e' b d, z)
    | 2::xs, .letE n t v b d   =>
      withLocalDeclD n (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.letE n t v e d, .letE n t v e' d, z)
                                                      
    | 0::xs, .lam n t b bi     => do let (e, e', z) ← visit fvars xs t; return (.lam n e b bi, .lam n e' b bi, z)
    | 1::xs, .lam n t b bi     =>
      withLocalDecl n bi (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.lam n t e bi, .lam n t e' bi, z)

    | 0::xs, .forallE n t b bi => do let (e, e', z) ← visit fvars xs t; return (.forallE n e b bi, .forallE n e' b bi, z)
    | 1::xs, .forallE n t b bi =>
      withLocalDecl n bi (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.forallE n t e bi, .forallE n t e' bi, z)

    | list, e                  => throwError m!"could not find subexpression {list} in '{e}'"
      
  visit #[] pos target



elab "tree_normalize " goalPos:treePos conv:conv : tactic =>
  let goalPos := getPosition goalPos
  workOnTreeAt goalPos fun pos pol tree => (do
    let (motive_core, rhs, proof, type) ← recurseToPosition tree conv pos
    let motive := Expr.lam `_a type motive_core .default
    let proof ← mkAppM (if pol then ``substitute else ``substitute') #[motive, proof]
    return { newTree := rhs, proof : TreeProof})

macro "tree_simp" goalPos:treePos : tactic => do `(tactic| tree_normalize $goalPos simp)

