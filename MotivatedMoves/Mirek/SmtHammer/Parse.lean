import MotivatedMoves.Mirek.SmtHammer.SmtExpr

namespace lispLexer

partial
def findStart (i : Nat) (s : String) : Nat :=
  if i >= s.length then i
  else
    let c := s.get (.mk i)
    if c = ' ' ∨ c = '\n' ∨ c = '\t' then
      findStart (i+1) s
    else
      i

partial
def findStop (i : Nat) (s : String) : Nat :=
  if i >= s.length then i
  else
    let c := s.get (.mk i)
    if c = ' ' ∨ c = '\n' ∨ c = '\t' ∨ c = '(' ∨ c = ')' then
      i
    else
      findStop (i+1) s

partial
def aux (i : Nat) (out : Array String) (s : String) : Array String :=
  let start := lispLexer.findStart i s
  if start >= s.length then out
  else
    let c0 := s.get (.mk start)
    let stop :=
      if c0 = '(' ∨ c0 = ')' then start+1
      else lispLexer.findStop (start+1) s
    aux stop (out.push (Substring.mk s (.mk start) (.mk stop)).toString) s

end lispLexer

partial
def lispLexer : String → Array String :=
  lispLexer.aux 0 #[]

namespace smtParser
def atom (s : String) : SmtExpr :=
  match s.toNat? with
  | .some n => .const n
  | .none => .str s

partial
def aux (i : Nat) (out : Array SmtExpr) (tokens : Array String) : Nat × (Array SmtExpr) :=
  if i >= tokens.size then (i, out)
  else
    let token := tokens.get! i
    if token = ")" then (i, out)
    else
      if token = "(" then
        let (i, subExprs) := aux (i+1) #[] tokens
        aux (i+1) (out.push (.list subExprs.toList)) tokens
      else
        aux (i+1) (out.push (atom token)) tokens

partial
def array (input_str : String) : Option (Array SmtExpr) :=
  let tokens := lispLexer input_str
  let (i, exprs) := aux 0 #[] tokens
  if i = tokens.size then exprs
  else none

partial
def singleton (input_str : String) : Option SmtExpr :=
  let res := array input_str
  match res with
  | .some #[res] => res
  | _ => none

end smtParser

def x := " ( this is 23 ( a ( lisp 2 1 ) 1 ( hehe )) )"

#eval
  match smtParser.singleton x with
  | .none => "none"
  | .some expr => expr.toString
