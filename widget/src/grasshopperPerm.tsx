import React, { useRef, useEffect } from 'react'

interface JumpButtonProps {
  pos : Set<string>
  order : string[]
  selected : Set<String>
  select (label : string) : void
  unselect (label : string) : void
}

function JumpButton(props : JumpButtonProps)
{
  var label : string
  if (props.pos.size == 0) label = '0'
  else {
    const jumps = Array.from(props.pos)
    jumps.sort()
    label = jumps.join('+')
  }
  const isSelected = (props.selected.has(label))
  const style = isSelected ? {backgroundColor: "yellow"} : {}
  var action : {(label : string) : void} = (_ : string) => {}
  if (props.pos.size > 0 && props.pos.size < props.order.length) {
    if (isSelected) action = props.unselect
    else action = props.select
  }

  return <td><button onClick={() => action(label)} style={style}>
    {label}
  </button></td>
}

interface JumpOrderProps {
  order : string[]
  selected : Set<String>
  select (label : string) : void
  unselect (label : string) : void
}
function JumpOrder(props : JumpOrderProps)
{
  var landings : Set<string>[] = [new Set()]
  const curPos : Set<string> = new Set()
  for (const jump of props.order) {
    curPos.add(jump)
    landings.push(new Set(curPos))
  }

  return <tr>
    {landings.map(pos => <JumpButton
      pos={pos} {...props}
    />)}
  </tr>
}

function permutator<T>(inputArr:T[]) : T[][] {
  var results:T[][] = [];

  function permute(arr : T[], memo : T[]) {
    var cur : T[]

    for (var i = 0; i < arr.length; i++) {
      cur = arr.splice(i, 1)
      if (arr.length === 0) {
        results.push(memo.concat(cur))
      }
      permute(arr.slice(), memo.concat(cur))
      arr.splice(i, 0, cur[0])
    }

    return results
  }

  return permute(inputArr, [])
}

function findMaxClique (incidence : boolean[][], start : number[] = []) : number[] {
  var res = start
  const firstNode : number = start.length > 0 ? start[start.length-1]+1 : 0
  console.log(firstNode)
  console.log(start)
  console.log(incidence)
  for (var i = firstNode; i < incidence.length; i++) {
    console.log(`every ${i}, ${start.every((x,_,__) => incidence[x][i])}`)
    if (start.every((x,_,__) => incidence[x][i])) {
      const cand = findMaxClique (incidence, start.concat([i]))
      if (cand.length > res.length) res = cand
    }
  }
  return res
}
function emptyGraph (numNodes : number) : boolean[][] {
  const res : boolean[][] = new Array(numNodes)
  for (var i = 0; i < numNodes; i++) {
    res[i] = new Array(numNodes)
    res[i].fill(false)
  }
  return res
}
function addEdge (incidence : boolean[][], a : number, b : number) : void {
  incidence[a][b] = true
  incidence[b][a] = true
}

interface MinesDisplayProps {
  mines : Set<String>
}

function MinesDisplay(props : MinesDisplayProps) {
  const mines_str = Array.from(props.mines)
  mines_str.sort()
  const mines = mines_str.map(s => s.split('+'))
  const incidence : boolean[][] = emptyGraph(mines.length)
  for (var a = 0; a < mines.length; a++)
    for (var b = a+1; b < mines.length; b++) {
      const m1 = mines[a]
      const m2 = mines[b]
      const m1s = new Set(m1)
      const m2s = new Set(m2)
      var missing1 = 0
      var missing2 = 0
      for (const x of m1) if (!m2s.has(x)) missing2 += 1
      for (const x of m2) if (!m1s.has(x)) missing1 += 1
      if (missing1 == 0 || missing2 == 0 || (missing1 == 1 && missing2 == 1))
        addEdge(incidence, a,b)
    }
  const clique = findMaxClique(incidence)

  return <div>
    <p>(at most) {mines_str.length} mines: {mines_str.join(', ')}</p>
    <p>{clique.length} different: {clique.map(i => mines_str[i]).join(', ')}</p>
  </div>
}

interface JumpsTableProps {
  jumps : string[]
}

export default function JumpsTable(props : JumpsTableProps) {
  const [selected, setSelected] = React.useState<Set<string>>(new Set())
  function select(label : string) {
    const s = new Set(selected)
    s.add(label)
    setSelected(s)
  }
  function unselect(label : string) {
    const s = new Set(selected)
    s.delete(label)
    setSelected(s)
  }

  return <div><table>
    { permutator(props.jumps).map(order =>
      <JumpOrder order={order} selected={selected} select={select} unselect={unselect}/>
    )}
  </table>
  <MinesDisplay mines = {selected}/>
  </div>
}
