import TreeMoves.Tree
import Mathlib.Lean.Meta.DiscrTree

namespace Tree

open Lean Meta DiscrTree


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

private def elimLooseBVarsByBeta (e : Expr) : CoreM Expr :=
  Core.transform e
    (pre := fun e => do
      if !e.hasLooseBVars then
        return .done e
      else if e.isHeadBetaTarget then
        return .visit e.headBeta
      else
        return .continue)


private def getKeyArgs (e : Expr) (isMatch root : Bool) : MetaM (Key s × Array Expr) := do
  let e ← reduceDT e root (simpleReduce := s)
  unless root do
    if let some v := toNatLit? e then
      return (.lit v, #[])
  match e.getAppFn with
  | .lit v         => return (.lit v, #[])
  | .const c _     =>
    if (← getConfig).isDefEqStuckEx && e.hasExprMVar then
      if (← isReducible c) then
        Meta.throwIsDefEqStuck
      else if let some matcherInfo := isMatcherAppCore? (← getEnv) e then
        let args := e.getAppArgs
        for arg in args[matcherInfo.getFirstDiscrPos: matcherInfo.getFirstDiscrPos + matcherInfo.numDiscrs] do
          if arg.hasExprMVar then
            Meta.throwIsDefEqStuck
      else if (← isRec c) then
        Meta.throwIsDefEqStuck
    let nargs := e.getAppNumArgs
    return (.const c nargs, e.getAppRevArgs)
  | .fvar fvarId   =>
    let nargs := e.getAppNumArgs
    return (.fvar fvarId nargs, e.getAppRevArgs)
  | .mvar mvarId   =>
    if isMatch then
      return (.other, #[])
    else do
      let ctx ← read
      if ctx.config.isDefEqStuckEx then
        return (.star, #[])
      else if (← mvarId.isReadOnlyOrSyntheticOpaque) then
        return (.other, #[])
      else
        return (.star, #[])
  | .proj s i a .. =>
    let nargs := e.getAppNumArgs
    return (.proj s i nargs, #[a] ++ e.getAppRevArgs)
  | .forallE _ d b _ =>
    let b ← if b.hasLooseBVars then elimLooseBVarsByBeta b else pure b
    if b.hasLooseBVars then
      return (.other, #[])
    else
      return (.arrow, #[d, b])
  | _ =>
    return (.other, #[])

private abbrev getMatchKeyArgs (e : Expr) (root : Bool) : MetaM (Key s × Array Expr) :=
  getKeyArgs e (isMatch := true) (root := root)

private abbrev getUnifyKeyArgs (e : Expr) (root : Bool) : MetaM (Key s × Array Expr) :=
  getKeyArgs e (isMatch := false) (root := root)

private abbrev findKey (cs : Array (Key s × Trie α s)) (k : Key s) : Option (Key s × Trie α s) :=
  cs.binSearch (k, default) (fun a b => a.1 < b.1)


partial def getUnifyWithSpecificity (d : DiscrTree α s) (e : Expr) : MetaM (Array (Array α × Nat)) :=
  withReducible do
    let (k, args) ← getUnifyKeyArgs e (root := true)
    match k with
    | .star => throwError "the unification pattern is a metavariable"--d.root.foldlM (init := #[]) fun result k c => process k.arity 0 #[] c result
    | _ =>
      let result ← match d.root.find? k with
        | none   => pure #[]
        | some c => process 0 1 args c #[]
      let result := result.qsort (·.2 > ·.2)
      match d.root.find? .star with
      | none => return result
      | some (.node vs _) => return result.push (vs, 0)
where
  process (skip : Nat) (specific : Nat) (todo : Array Expr) (c : Trie α s) (result : Array (Array α × Nat)) : MetaM (Array (Array α × Nat)) := do
    match skip, c with
    | skip+1, .node _  cs =>
      if cs.isEmpty then
        return result
      else
        cs.foldlM (init := result) fun result ⟨k, c⟩ => process (skip + k.arity) specific todo c result
    | 0, .node vs cs => do
      if todo.isEmpty then
        return result.push (vs, specific)
      else if cs.isEmpty then
        return result
      else
        let e     := todo.back
        let todo  := todo.pop
        let (k, args) ← getUnifyKeyArgs e (root := false)
        let visitStar (result : Array (Array α × Nat)) : MetaM (Array (Array α × Nat)) :=
          let first := cs[0]!
          if first.1 == .star then
            process 0 specific todo first.2 result
          else
            return result
        let visitNonStar (k : Key s) (args : Array Expr) (result : Array (Array α × Nat)) : MetaM (Array (Array α × Nat)) :=
          match findKey cs k with
          | none   => return result
          | some c => process 0 (specific + 1) (todo ++ args) c.2 result
        match k with
        | .star  => cs.foldlM (init := result) fun result (k, c) => process specific k.arity todo c result
        | .arrow => visitStar (← visitNonStar .other #[] (← visitNonStar k args result))
        | _      => visitStar (← visitNonStar k args result)



def VarRec : OptionRecursor MetaM α where
  imp_right _ _ _ k := do k
  imp_left  _ _ _ k := do k
  and_right _ _ _ k := do k
  and_left  _ _ _ k := do k

  all  _ _ _ pol _ k := do
    let var ← if  pol then Expr.fvar <$> mkFreshFVarId else Expr.mvar <$> mkFreshMVarId
    k var
  ex   _ _ _ pol _ k := do
    let var ← if !pol then Expr.fvar <$> mkFreshFVarId else Expr.mvar <$> mkFreshMVarId
    k var
  inst _ _ _ pol _ k := do
    let var ← if  pol then Expr.fvar <$> mkFreshFVarId else Expr.mvar <$> mkFreshMVarId
    k var


def getSubexprUnify (d : DiscrTree α s) (e : Expr) (path : List TreeBinderKind) (pos : List Nat) : MetaM (Array (Array α × Nat)) := do
  VarRec.recurse true e path fun _pol e _path =>
    let rec getSubexpr (fvars : Array Expr): List Nat → Expr → MetaM (Array (Array α × Nat))
      | xs   , .mdata _ b        => getSubexpr fvars xs b

      | []   , e                 => getUnifyWithSpecificity d e
      
      | 0::xs, .app f _          => getSubexpr fvars xs f
      | 1::xs, .app _ a          => getSubexpr fvars xs a

      | 0::xs, .proj _ _ b       => getSubexpr fvars xs b

      | 0::xs, .letE _ t _ _ _   => getSubexpr fvars xs t
      | 1::xs, .letE _ _ v _ _   => getSubexpr fvars xs v
      | 2::xs, .letE n t _ b _   =>
        withLocalDeclD n (t.instantiateRev fvars) fun fvar => getSubexpr (fvars.push fvar) xs b
                                                        
      | 0::xs, .lam _ _ b _     => getSubexpr fvars xs b
      | 1::xs, .lam n t b _     =>
        withLocalDeclD n (t.instantiateRev fvars) fun fvar => getSubexpr (fvars.push fvar) xs b

      | 0::xs, .forallE _ _ b _ => getSubexpr fvars xs b
      | 1::xs, .forallE n t b _ =>
        withLocalDeclD n (t.instantiateRev fvars) fun fvar => getSubexpr (fvars.push fvar) xs b
      | list, e                  => throwError m!"could not find subexpression {list} in '{e}'"

    getSubexpr #[] pos e

def filterLibraryResults («matches» : Array (Array α × Nat)) (filter : α → MetaM Bool) (minimum : Option Nat := some 6) : MetaM (Array (Array α × Nat)) := do
  let mut result := #[]
  let mut total := 0
  for (candidates, specific) in «matches» do
    if minimum.elim false (total ≥ ·) then
      return result
    let filtered ← candidates.filterM filter
    unless filtered.isEmpty do
      result := result.push (filtered, specific)
      total := total + filtered.size
  return result
