import TreeMoves.TreeRewrite

namespace Tree

open Lean Elab Tactic Meta


def normalize (norm : Expr → MetaM (Expr × Expr)) (fvars : Array Expr) (lhs : Expr) : MetaM RewriteInfo := do
  let (rhs, proof) ← norm (lhs.instantiateRev fvars)
  
  let lctx ← getLCtx

  let n := fvars.size
  let motive_core := n.fold (.bvar · |> mkApp ·) (.bvar n)

  let proof ← fvars.foldrM (fun fvar proof => mkAppM ``funext #[lctx.mkLambda #[fvar] proof]) proof
  let type := lctx.mkForall fvars (← inferType rhs)
  let rhs := rhs.abstract fvars

  return (motive_core, rhs, proof, type)


private def recurseToPosition (norm : Expr → MetaM (Expr × Expr)) (target : Expr) (pos : List Nat) : MetaM RewriteInfo :=
  
  let rec visit (fvars : Array Expr) : List Nat → Expr → MetaM RewriteInfo
    | xs   , .mdata d b        => do let (e, e', z) ← visit fvars xs b; return (.mdata d e, .mdata d e', z)

    | []   , e                 => normalize norm fvars e
    
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




def simpMove (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (target : Expr) : MetaM (Expr × Expr) := do
  let (r, _) ← simp target ctx discharge? {}
  match r.proof? with
  | some proof => return (r.expr, proof)
  | none => throwError m! "could not simplify {target}"

def getSimpContext : MetaM Simp.Context := do
  let mut simpTheorems : SimpTheoremsArray := #[← getSimpTheorems]
  for h in ← getPropHyps do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (.fvar h)
  return { simpTheorems }

def defaultSimpMove (target : Expr) : MetaM (Expr × Expr) :=
  do simpMove (← getSimpContext) none target



elab "tree_simp" goalPos:treePos : tactic =>
  let goalPos := getPosition goalPos
  workOnTreeAt goalPos fun pos pol tree => (do
    let (motive_core, rhs, proof, type) ← recurseToPosition defaultSimpMove tree pos
    let motive := Expr.lam `_a type motive_core .default
    let proof ← mkAppM (if pol then ``substitute else ``substitute') #[motive, proof]
    if pos == [] then
      let isConstOf := (Expr.consumeMData rhs).isConstOf
      if pol
      then if isConstOf `True then
        return { proof := mkApp proof (.const `True.intro [])}
      /- need to add a few more lemmas in Tree.lean for the False case to work. -/
      -- else if isConstOf `False then
      --   return { proof }
    
    return { newTree := rhs, proof })

