import Std.Data.List.Basic

inductive Tree (α : Type) := 
  | node (value : α) (children : List (Tree α)) : Tree α
  | metaNode (metaChildren : (List (Tree α))) : Tree α
deriving BEq

def treeListToString [ToString α] (treeList : List (Tree α)) : String :=  
  let rec treeToString : Tree α → String
      | .node v [] => toString v
      | .node v c => toString v ++ " [" ++ treeListToString c ++ "]"
      | .metaNode c => "{" ++ treeListToString c ++ "}"
  match treeList with
  | [] => ""
  | [x] => treeToString x 
  | x :: xs => (treeToString x) ++ ", " ++ treeListToString xs

instance [ToString α] : ToString (Tree α) where 
  toString t := treeListToString [t]

instance : Inhabited (Tree α) where 
  default := .metaNode []

def Tree.size : Tree α → Nat 
  | node _ [] 
  | metaNode [] => 1 
  | node v (x::xs) => x.size + (node v xs).size
  | metaNode (x::xs) => x.size + (metaNode xs).size   

-- it is also useful to have this notion for a list of trees
def size : List (Tree α) → Nat 
  | [] => 0
  | x::xs => x.size + size xs

def Tree.leaf (value : α) : Tree α := Tree.node value []

-- Examples
def aPlusB : Tree String := .node "+" [.leaf "a", .leaf "b"]
#eval aPlusB
#eval aPlusB.size == 3

def twiceAPlusB : Tree String := .node "+" [aPlusB, aPlusB]
#eval twiceAPlusB

def t3 : Tree String := .node "*" [.metaNode [aPlusB, .node "+" [.leaf "b", .leaf "c"]], aPlusB]
#eval t3

-- Equivalence of Trees respecting that children of meta nodes are not ordered 
def List.equalUpToPermutation [BEq α] : List α → List α → Bool 
  | [], [] => true
  | [], _ => false
  | x :: xs, ys => if ys.contains x 
                   then equalUpToPermutation xs (ys.erase x) else false

def Tree.equivalentTo [BEq α]: Tree α → Tree α → Bool
  | node v [], node w [] => if v==w then true else false 
  | node v (x::xs), node w (y::ys) => 
    if x==y then (node v xs).equivalentTo (node w ys) 
            else false 
  | metaNode xs, metaNode ys => List.equalUpToPermutation xs ys
  | _, _ => false

-- Two auxiliary functions on lists
def zipWithAndRemainder (f : α → α → β) : (xs : List α) → (ys : List α) → List β × List α 
  | xs, []
  | [], xs => ([], xs)
  | x::xs, y::ys => let (zipped, remainder) := zipWithAndRemainder f xs ys 
                    (f x y :: zipped, remainder)

def shorterLonger (xs : List α) (ys : List α) : List α × List α := 
  if xs.length < ys.length then (xs, ys) else (ys, xs)

-- Calculating tree edit distance and least common generalizer  
namespace leastCommonGeneralizer

structure Computation (α : Type) where  
  generalizer : Tree α 
  distance : Nat 
deriving BEq

instance : Inhabited (Computation α) where 
  default := ⟨.metaNode [], 0⟩ 

instance [ToString α] : ToString (Computation α) where 
  toString c := toString c.generalizer  ++ " | " ++ toString c.distance

instance : HAdd (Computation α) Nat (Computation α) where 
  hAdd c a := {c with distance := c.distance + a}

def distances (xs : List (Computation α)) : List Nat := 
  xs.map (fun x => x.distance)

def generalizers (xs : List (Computation α)) : List (Tree α) := 
  xs.map (fun x => x.generalizer)

def cumulativeDistance (xs : List (Computation α)) : Nat := 
  (distances xs).foldl (· + ·) 0 

def computationWithMinimalDistance : (xs : List (Computation α)) → Computation α  
  | [x] => x
  | x :: xs => let currentMinimizer := computationWithMinimalDistance xs
             if currentMinimizer.distance < x.distance then currentMinimizer else x
  | [] => dbg_trace "Cannot have minimizer of emtpy set"; default -- should never occur 

-- Minimal matchings implemented in a brute force way
def allMatchings (n : Nat) (m : Nat) : List (List Nat) := 
  match n with 
  | 0 => []
  | 1 => (List.range m).map (fun x => [x])
  | n + 1 => let matchingsN := allMatchings n m
             let notInMatching (matching : List Nat) : List Nat := (List.range m).removeAll matching
             List.join (matchingsN.map (fun matchingN => 
             let elementsThatNPlusOneCanMapTo := notInMatching matchingN
             elementsThatNPlusOneCanMapTo.map (fun newElem => matchingN ++ [newElem])
             ))

def cost (matrix : List (List Nat)) (matching : List Nat) : Nat := 
  let costs := matching.mapIdx (fun idx m => matrix[idx]![m]!)
  costs.foldl (· + ·) 0

def minimalMatching (matrix : List (List Nat)) : Nat × (List Nat) :=
  let n := matrix.length
  let m := matrix[0]!.length
  let allMatchings := allMatchings n m
  let costOfMatchings := allMatchings.map (fun matching => cost matrix matching)
  match List.minimum? costOfMatchings with 
    | some minimum => 
    let idxOfMinimalMatching := costOfMatchings.indexOf minimum
    (minimum, allMatchings[idxOfMinimalMatching]!)
    | none => dbg_trace "No minimal matching found, the given cost matrix must be empty"; (0, [])

def mapFromList (m : List Nat) : (Nat → Nat) := 
  fun i => match m[i]? with 
  | none => m.length 
  | some v => v

-- Distance rationale: The cost for deleting a tree is its size, creating a new meta node creates an additional cost of 1 
open Tree in 
partial def compute [BEq α] [ToString α] (tree1 : Tree α) (tree2 : Tree α) : Computation α := 
  let computeAgainstList (t : Tree α) (xs : List (Tree α)) : Computation α := 
    if xs == [] then 
    ⟨metaNode [], t.size + 1⟩ 
  else
    let computations := xs.map (fun x => compute t x)
    let minimizer := computationWithMinimalDistance computations
    let generalizer := .metaNode [minimizer.generalizer]
    let distance := minimizer.distance + size (xs.erase minimizer.generalizer) + 1
    ⟨generalizer, distance⟩
  
  match tree1, tree2 with
  | node v [], node w [] => if v==w then ⟨node v [], 0⟩ else ⟨metaNode [], 1⟩
  | metaNode xs, metaNode [] 
  | metaNode [], metaNode xs => ⟨metaNode [], size xs⟩ 
  | node v xs, metaNode ys 
  | metaNode ys, node v xs => dbg_trace "Comparing node to meta node"
                              computeAgainstList (node v xs) ys

  | metaNode xs, metaNode ys => let (shorter, longer) := shorterLonger xs ys
                                let m := longer.length 

                                let computations := shorter.map (fun a => longer.map (fun b => compute a b))
                                let costMatrix := computations.map (fun as => as.map (fun b => b.distance))
                                let (cost, matchingList) := minimalMatching costMatrix
                                let IdxsOfChildrenNotInMatching := (List.range m).removeAll matchingList
                                let matching := mapFromList matchingList
                                
                                let costOfDeletingChildren := size (IdxsOfChildrenNotInMatching.map (fun i => longer[matching i]!))
                                let distance := cost + costOfDeletingChildren
                                let resultingChildren := computations.mapIdx (fun i x => x[matching i]!.generalizer)
                                let generalizer := metaNode resultingChildren 

                                ⟨generalizer, distance⟩  

  | node v xs, node w ys => let computeNodesWithDifferentValue (lvalue : α) (ls : List (Tree α))
                                                               (rvalue : α) (rs : List (Tree α)) : Computation α := 
                                let leftInRight := computeAgainstList (node lvalue ls) rs + 1
                                let rightInLeft := computeAgainstList (node rvalue rs) ls + 1
                                let bothMetified := compute (metaNode ls) (metaNode rs) + 2
                                computationWithMinimalDistance [leftInRight, rightInLeft, bothMetified]    

                            if v == w && xs.length == ys.length then 
                              let computations := List.zipWith compute xs ys
                              let distance := cumulativeDistance computations
                              let generalizer := node v (generalizers computations)
                              if distance == 0 then 
                                ⟨generalizer, distance⟩  
                              else
                                computationWithMinimalDistance [⟨generalizer, distance⟩, 
                                                                computeNodesWithDifferentValue v xs w ys]
                            else 
                              computeNodesWithDifferentValue v xs w ys


-- Some first testing: 
#eval compute aPlusB aPlusB

def test0 : Tree String := (.node "+" [.leaf "c", aPlusB]) 
#eval (aPlusB, test0)
#eval compute aPlusB test0

def test1 : Tree String := (.node "+" [aPlusB, .node "+" [.leaf "c", .leaf "b"]])
#eval (aPlusB, test1)
#eval compute aPlusB test1
#eval compute (.leaf "a") aPlusB

def test2 : Tree String := .node "+" [.node "+" [.leaf "c", .leaf "b"], aPlusB]
def test3 : Tree String := .node "+" [aPlusB, .node "+" [.node "+" [.leaf "d", .leaf "c"], aPlusB]]
#eval (test2, test3)
#eval compute test2 test3

-- More involved trees
def repeatN (x : α) (f : α → α) : Nat → α 
  | 0 => x
  | n+1 => f (repeatN x f n)

def largeTree (n : Nat) : Tree String := repeatN (.leaf "0") (fun x => Tree.node "+" [x, x]) n
#eval largeTree 2
#eval compute (largeTree 4) (.node "*" [largeTree 4]) 
-- 4 is still relatively fast, but 5 takes quite long

def square (t : Tree String) : Tree String := .node "(^2)" [t]

#eval repeatN aPlusB square 3
-- If n >= 3 the following gives unsatisfactory results, the common substructure of + [a, b] is not detected. 
#eval compute aPlusB (repeatN aPlusB square 3) -- even 100 still works after some time
-- This is because of the the tree being deep which requires creating many nested meta nodes (= expensive)
-- A way out could be to have meta node collapsing, i.e. a rule like 
-- metaNode [metaNode x1, ..., metaNode xn] => metaNode [x1, ..., xn]

#eval repeatN aPlusB (fun x => Tree.node "+" [x, x]) 1
#eval compute aPlusB (repeatN aPlusB (fun x => Tree.node "+" [x, x]) 3) -- more difficult but still fine for small values 

