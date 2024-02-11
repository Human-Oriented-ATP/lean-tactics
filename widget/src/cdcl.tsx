import React, { useMemo, useRef, useEffect } from 'react'

type Variable = string

interface Literal {
  v : Variable
  pos : boolean
}

class LiteralList {
  lits : Literal[]
  posVars : Set<Variable>
  negVars : Set<Variable>

  constructor (lits : Literal[]) {
    this.posVars = new Set()
    this.negVars = new Set()
    this.lits = []
    for (const l of lits) this.push(l)
  }
  has (l : Literal) {
    if (l.pos) return this.posVars.has(l.v)
    else return this.negVars.has(l.v)
  }
  hasNeg (l : Literal) {
    if (l.pos) return this.negVars.has(l.v)
    else return this.posVars.has(l.v)
  }
  push(l : Literal) {
    const s = l.pos ? this.posVars : this.negVars
    if (s.has(l.v)) return
    s.add(l.v)
    this.lits.push(l)  
  }
  pop() : Literal | undefined {
    const res = this.lits.pop()
    if (res !== undefined) {
      const s = res.pos ? this.posVars : this.negVars
      s.delete(res.v)
    }
    return res
  }
  isSubsetOf(other : LiteralList) : boolean {
    for (const v of this.posVars)
      if(!other.posVars.has(v)) return false
    for (const v of this.negVars)
      if(!other.negVars.has(v)) return false
    return true
  }
  clone() {
    return new LiteralList(this.lits)
  }
}
type Clause = LiteralList

function resolution(clause1 : Clause, clause2 : Clause, v : Variable) : Clause {
  return new LiteralList(
    clause1.lits.filter(l => !(l.pos && l.v == v)).concat(
      clause2.lits.filter(l => !(!l.pos && l.v == v))
    )
  )
}

function filterClause(clause : Clause, assumps : LiteralList) : Clause | undefined {
  const lits = []
  for (const l of clause.lits) {
    if (assumps.has(l)) return
    else if(!assumps.hasNeg(l)) lits.push(l)
  }
  return new LiteralList(lits)
}

function addClause(clauses : Clause[], clause : Clause) : Clause[] {
  const res = clauses.filter(cl => (!clause.isSubsetOf(cl)))
  for (const cl of res) {
    if (cl.isSubsetOf(clause)) return res
  }
  res.push(clause)
  return res
}

interface CDCLState {
  assumps : LiteralList
  globalClauses : Clause[]
  clauses : Clause[]
  contr? : [Clause, Clause, Variable]
}
function makeCDCLState(assumps : LiteralList, globalClauses : Clause[]) : CDCLState {
  const res : CDCLState = {
    assumps : assumps,
    globalClauses : globalClauses,
    clauses : [],
  }
  const posToClause = new Map<Variable, Clause>()
  const negToClause = new Map<Variable, Clause>()
  for (const globalClause of globalClauses) {
    const clause = filterClause(globalClause, assumps)
    if (clause === undefined) continue
    if (clause.lits.length == 1) {
      const l = clause.lits[0]
      if (l.pos) posToClause.set(l.v, globalClause)
      else negToClause.set(l.v, globalClause)
    }
    res.clauses = addClause(res.clauses, clause)
  }
  if (res.clauses.length == 1) return res
  for (const [v, clause1] of posToClause) {
    const clause2 = negToClause.get(v)
    if (clause2 !== undefined) {
      res.contr = [clause1, clause2, v]
      break
    }
  }
  res.clauses.sort((a,b) => (a.lits.length - b.lits.length))
  return res
}

function litToStr(l : Literal) : string {
  if (l.pos) return l.v
  else return '¬'+l.v
}

function InteractiveClause(props : {clause : Clause, selectLit (l : Literal) : void }) : JSX.Element {
  if (props.clause.lits.length == 0) return <li>Contradiction</li>
  const parts : JSX.Element[] = []
  for (const lit of props.clause.lits) {
    parts.push(<a className="pointer" onClick={() => { props.selectLit(lit) }}>{litToStr(lit)}</a>)
    parts.push(<> ∨ </>)
  }
  parts.pop()
  return <li>{parts}</li>
}
function InteractiveClauses(props : {clauses : Clause[], selectLit (l : Literal) : void }) : JSX.Element {
  return <ul>
    {props.clauses.map(clause =>
    <InteractiveClause clause={clause} selectLit={props.selectLit} />
    )}
  </ul>
}

export default function InteractiveCDCL(props : { startClauses : Literal[][] }) : JSX.Element {
  const [assumps, setAssumps] = React.useState<LiteralList>(new LiteralList([]))
  const [globClauses, setGlobClausesRaw] = React.useState<Clause[]>([])
  function setGlobClauses(nextClauses : Clause[]) {
    nextClauses.sort((a,b) => (a.lits.length - b.lits.length))
    setGlobClausesRaw(nextClauses)
  }
  const [autoResolution, setAutoResolution] = React.useState<boolean>(false)
  const [autoBacktracking, setAutoBackTracking] = React.useState<boolean>(false)
  const [autoUnitProp, setAutoUnitProp] = React.useState<boolean>(false)
  React.useMemo(() => {
    setGlobClauses(
      props.startClauses.map(clause => new LiteralList(clause))
    )
  }, [])
  const state = makeCDCLState(assumps, globClauses)

  var autoState = state

  // Automation
  for (var x = 0;; x++) {
    if (x == 100000) {
      autoState = state
      break
    }
    if (autoBacktracking &&
      autoState.clauses.length == 1 && autoState.clauses[0].lits.length == 0 && autoState.assumps.lits.length > 0) {
      const nextAssumps = autoState.assumps.clone()
      nextAssumps.pop()
      autoState = makeCDCLState(
        nextAssumps, autoState.globalClauses
      )
    }
    else if (autoResolution &&
      autoState.contr !== undefined) {
        const [clause1, clause2, v] = autoState.contr
        autoState = makeCDCLState(
          autoState.assumps,
          addClause(autoState.globalClauses, resolution(clause1, clause2, v))
        )
      }
    else if (autoUnitProp && autoState.clauses.length > 0 && autoState.clauses[0].lits.length == 1) {
      const nextAssumps = autoState.assumps.clone()
      for (const clause of autoState.clauses) {
        if (clause.lits.length == 1)
          nextAssumps.push(clause.lits[0])
      }
      autoState = makeCDCLState(
        nextAssumps, autoState.globalClauses
      )
    }
    else break
  }
  if (autoState !== state) {
    setAssumps(autoState.assumps)
    setGlobClauses(autoState.globalClauses)
  }

  function selectLit(lit : Literal) {
    const nextAssumps = assumps.clone()
    nextAssumps.push(lit)
    setAssumps(nextAssumps)
  }
  function backtrack() {
    if (assumps.lits.length == 0) return
    const nextAssumps = assumps.clone()
    nextAssumps.pop()
    setAssumps(nextAssumps)
  }
  function getContr() {
    if (state.contr === undefined) return
    const [clause1, clause2, v] = state.contr
    setGlobClauses(addClause(globClauses, resolution(clause1, clause2, v)))
  }

  const parts : JSX.Element[] = []

  parts.push(
    <form>
      <p>Automation:</p>
      <label>
        <input type="checkbox" onChange={e => {
          setAutoResolution(e.target.checked)
        }}/>
        <span> Resolution</span>
      </label><br/>
      <label>
        <input type="checkbox" onChange={e =>
          setAutoBackTracking(e.target.checked)
        }/>
        <span> Backtracking</span>
      </label><br/>
      <label>
        <input type="checkbox" onChange={e =>
          setAutoUnitProp(e.target.checked)
        }/>
        <span> Unit Propagation</span>
      </label><br/>
      <hr/>
    </form>
  )

  if (state.contr !== undefined) {
    parts.push(<button onClick={getContr}>Derive contradiction</button>)
  }
  if (assumps.lits.length > 0) {
    parts.push(<>
      <p>Assumed: {assumps.lits.map(litToStr).join(', ')} <button onClick={backtrack}>{"<"}</button></p>
      </>)
    if (state.clauses.length > 0)
      parts.push(<>
        <p>Clauses:</p>
        <InteractiveClauses clauses={state.clauses} selectLit={selectLit}/>  
      </>)
    else
        parts.push(<p>All clauses are satisfied!</p>)
  }

  parts.push(<>
    <p>Global clauses:</p>
    <InteractiveClauses clauses={globClauses} selectLit={selectLit}/>
  </>)

  return <div>
    {parts}
  </div>
}
