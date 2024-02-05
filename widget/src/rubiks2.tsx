import * as THREE from 'three';
import * as React from 'react';
import { DocumentPosition, RpcContext } from '@leanprover/infoview';
import { TrackballControls } from '@react-three/drei';
import { Canvas } from '@react-three/fiber';

type rubikscolor =
  | "white" | "blue" | "red" | "yellow" | "green" | "orange" | "empty"

const rubikscolor_to_webcolor = {
  "white" : "snow",
  "blue" : "blue",
  "red" : "red",
  "yellow" : "yellow",
  "green" : "green",
  "orange" : "darkorange",
  "empty" : "dimgray",
}

type genstr =
  | "U" | "D" | "L" | "R" | "F" | "B"
  | "U'" | "D'" | "L'" | "R'" | "F'" | "B'" | ""

function generatorToRotation(generator: string, cubelet: string, time = 1.0): THREE.Matrix4 {
  if (generator.includes("'")) {
    return generatorToRotation(generator.split("'")[0], cubelet, time).invert()
  }
  const θ = Math.PI * 0.5 * time
  if (generator == "R" && cubelet[0] == "2") {
    return new THREE.Matrix4().makeRotationX(-θ)
  }
  if (generator == "L" && cubelet[0] == "0") {
    return new THREE.Matrix4().makeRotationX(θ)
  }
  if (generator == "U" && cubelet[1] == "2") {
    return new THREE.Matrix4().makeRotationY(-θ)
  }
  if (generator == "D" && cubelet[1] == "0") {
    return new THREE.Matrix4().makeRotationY(θ)
  }
  if (generator == "F" && cubelet[2] == "2") {
    return new THREE.Matrix4().makeRotationZ(-θ)
  }
  if (generator == "B" && cubelet[2] == "0") {
    return new THREE.Matrix4().makeRotationZ(θ)
  }
  // console.warn(`Invalid generator ${generator}. Skipping.`)
  return new THREE.Matrix4()
}

function* prod(...iters: any[]): Generator<any[]> {
  if (iters.length === 0) {
    yield []
    return
  }
  let [xs, ...rest] = iters // [fixme] need to Tee the iters.
  for (let x of xs) {
    const whatever = prod(...rest)
    for (let ys of whatever) {
      yield [x, ...ys]
    }
  }
}

const cubelets = [...prod([0, 1, 2], [0, 1, 2], [0, 1, 2])].map(x => x.join(""))

interface CubeletProps {
//  cube : Array;
  time: number;
  move: genstr;
  cube: rubikscolor[][];
  cid: string;
}

function Cubelet(props: CubeletProps) {
  const me = React.useRef<THREE.Mesh | null>(null)

  React.useEffect(() => {
    const m = generatorToRotation(props.move, props.cid, props.time ?? 0.0)
    const pos: [number, number, number] =
      props.cid.split("").map(x => (Number(x) - 1) * (1.0 + 0.1)) as any
    const trans = new THREE.Matrix4().makeTranslation(...pos)
    m.multiply(trans)
    if (me.current) {
      me.current.setRotationFromMatrix(m)
      me.current.position.setFromMatrixPosition(m)
    }
  }, [props.cid, props.time, props.move])
  var rcolors : rubikscolor[] = Array(6).fill("empty")
  var x,y,z
  [x,y,z] = props.cid.split("").map(Number)
  if (x == 2) // R
    rcolors[0] = props.cube[3][(2-z) + 3*(2-y)];
  if (x == 0) // L
    rcolors[1] = props.cube[1][z + 3*(2-y)];
  if (y == 2) // U
    rcolors[2] = props.cube[0][x + 3*z];
  if (y == 0) // D
    rcolors[3] = props.cube[4][x + 3*(2-z)];
  if (z == 2) // F
    rcolors[4] = props.cube[2][x + 3*(2-y)];
  if (z == 0) // B
    rcolors[5] = props.cube[5][x + 3*y];
  var wcolors = rcolors.map((c : rubikscolor) => rubikscolor_to_webcolor[c])
  return (
    <mesh ref={me}>
      <boxGeometry args={[1, 1, 1]} />
      {wcolors.map((col, idx) => (
        <meshPhongMaterial key={idx} attach={`material-${idx}`} color={col} />
      ))}
    </mesh>
  )
}

interface CubeProps {
  time: number;
  move: genstr;
  cube: rubikscolor[][];
  last?: rubikscolor[][] | null;
}

function Cube(props: CubeProps) {
  return <group>
    {cubelets.map(cubelet =>
      <Cubelet key={cubelet} cid={cubelet} time={props.time} move={props.move} cube={props.cube} />)}
  </group>
}

export default function (props: any) {
  const rs = React.useContext(RpcContext)
  const cube = React.useRef<rubikscolor[][]>(props.cube)
  const [cubeProps, setProps] = React.useState<CubeProps>({time:0.0, move:"", cube:props.cube})
  const timer = React.useRef<any>(null)
  const t = cubeProps.time

  function setPropsD(msg:string, nextProps:CubeProps) {
    //console.log(msg)
    //console.log(nextProps.time)
    //console.log(nextProps.cube)
    setProps(nextProps)
  }
  function setT(nextT:number) {
    setPropsD("setT",{
      time:nextT, move:cubeProps.move,
      cube:cubeProps.cube, last:cubeProps.last
    })
  }

  if (timer.current === null && t < 0) {
    var nextT = t + 0.15
    if (nextT >= 0) nextT = 0
    timer.current = setTimeout(
      () => {
        timer.current = null
        setT(nextT)
      },
      50
    )
  }
  function cancel_animation() {
    if(timer.current !== null) {
      clearTimeout(timer.current)
      timer.current = null
    }
  }

  async function find_move(cube1 : rubikscolor[][], cube2 : rubikscolor[][]) {
    const m = await rs.call<rubikscolor[][][], genstr>(
      'Rubik.detectMoveQuery',
      [cube1, cube2])
    if (""+cube.current != ""+cube2) return
    var startT = -1.0
    if (""+cubeProps.last == ""+cube2)
      startT -= t;
    // console.log(`startT = ${startT}`)
    cancel_animation()
    if (m == "")
      setPropsD("cancel", {cube:cube2, time:0.0, move:"", last:cube1})
    else
      setPropsD("activate", {cube:cube2, time:startT, move:m, last:cube1})
  }

  if (""+props.cube != ""+cube.current) {
    // console.log("Input")
    // console.log(props.cube)
    const last = cube.current
    cube.current = props.cube
    find_move(last, props.cube)
  }

  return <details open={true}><div style={{ height: 320 }}>
    <Canvas >
      <pointLight position={[150, 150, 150]} intensity={0.55} />
      <ambientLight color={0xffffff} />
      <group rotation-x={Math.PI * 0.25} rotation-y={Math.PI * 0.25}>
        <Cube move={cubeProps.move} time={t} cube={cubeProps.cube} />
      </group>
      <TrackballControls rotateSpeed={5.0} />
    </Canvas>
  </div></details>
}
