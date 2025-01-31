import Mathlib.Algebra.Order.Ring.WithTop
open Classical Std

-- I did algorithmic verification for my last project, and wanted to continue
-- The goal is write an implementation of, and prove correctness of Bellman-Ford
-- BF is a shortest path algorithm, which takes a graph (with potentially negative edges)
-- and a source, and returns the shortest path from the source to all vertices OR
-- if the graph contains a cycle with negative total weight, it reports so
-- This is desirable because shortest paths are undefined on graphs with negative cycles
-- Detailed description here: https://web.stanford.edu/class/archive/cs/cs161/cs161.1168/lecture14.pdf

-- We're working with finite graphs, therefore there should be an encoding from vertices to naturals
-- This can easily be extended to work for generically typed vertices (as long as they satisfy the hash map properties)
abbrev Vertex := Nat

-- We want integer weights because Bellman-Ford is an algorithm which specifically
-- is powerful because it deals with negative edges
abbrev Weight := Int

-- We will assume directed graphs, since undirected can be accounted for with adding the same edge backwards
-- That is, an undirected graph is just a special case of a directed graph
abbrev Edge := (Vertex × Vertex × Weight)

-- Representation of graph as an adjacency table, mapping vertices to their out-neighbors
abbrev Graph := List (Vertex × (List (Vertex × Weight)))

-- Define a mapping of shortest paths as vertices to infinity or a distance
-- Using WithTop as our reprensation of infinity
abbrev PathDistances := List (Vertex × (WithTop Weight))

-- -- Checks if two maps are equal. I feel like I shouldn't have to write this
-- -- But I couldn't figure out how to get lean to be able to decide this
-- def mapsEq (l r : PathDistances) : Bool :=
--   let compKeys := l.map (fun key val => val == r.getD key none)
--   compKeys.fold (fun acc _ same => same && acc) true

-- Graph construction / manipulation functions
-- Creates an empty graph
def emptyGraph : Graph := []

-- Adds a vertex with no neighbors
def addVertex (G : Graph) (v : Vertex): Graph :=
  match G with
  | [] => [(v, [])]
  | (vert, edges) :: rest => if vert = v then G else (vert, edges) :: addVertex rest v

-- This also inserts both vertices into the graph if they do not exist
def addEdge (G : Graph) (e : Edge) : Graph :=
  let (u, v, w) := e
  let G' := addVertex (addVertex G u) v

  G'.map (fun (vert, edges) => if vert = u then (vert, (v, w) :: edges) else (vert, edges))

-- Creates a graph given a list of edges
def fromEdges (edges : List Edge) : Graph := edges.foldl addEdge emptyGraph

-- Returns the out-edges of a vertex
def getOutEdges (G : Graph) (v : Vertex) : List (Vertex × Weight) :=
  match G with
  | []  => []
  | (vert, edges) :: rest  => if vert = v then edges else getOutEdges rest v

-- Returns the out-neighbors of a vertex
def getOutNeighbors (G : Graph) (v : Vertex) : List Vertex :=
  let outPairs := getOutEdges G v
  outPairs.map (fun (vert, _) => vert)

def getInEdges (G : Graph) (v : Vertex) : List (Vertex × Weight) :=
  G.foldl (fun acc (vert, edges) =>
    edges.foldl (fun acc' (vert', weight) =>
      if vert' = v then (vert, weight) :: acc' else acc'
    ) acc
  ) []

-- Returns the in-neighbors of a vertex, with the
def getInNeighbors (G : Graph) (v : Vertex) : List Vertex :=
  let inPairs := getInEdges G v
  inPairs.map (fun (vert, _) => vert)

-- End graph library

-- Bellman-Ford Implementation
-- This performs the relaxation step of the Bellman-Ford algorithm for a particuar vertex
def extendShortestPath (G : Graph) (prevDists : PathDistances) (pair : Vertex × WithTop Weight) : Vertex × WithTop Weight :=
  let (v, vDist) := pair
  let inEdges := getInEdges G v
  inEdges.foldl (fun acc (inNeighbor, edgeWeight) =>
    let neighborDist := prevDists.findSome? (fun (vert, dist) => if vert = inNeighbor then dist else none)
    match vDist, neighborDist with
    | some dist, some neighborDist => (v, min (neighborDist + edgeWeight) dist)
    | none, some neighborDist => (v, neighborDist + edgeWeight)
    | _, _ => acc
  ) pair

-- The meat of the bellman ford algorithm. Given the previous shortest path distances,
-- updates them by looking at every edge. Terminates after we've done as many rounds
-- as there vertices in the graph.
def BF_loop (G : Graph) (dists : PathDistances) (hops : Nat) : Bool × PathDistances  :=
  if hops = 0
  -- If we're ever here, then our distances haven't converged after |V| rounds
  -- Indicating a negative cycle, so no shortest paths
  -- We return a booolean here to indicate that shortest paths are not possible
  then ⟨false, ∅⟩
  else
  -- update shortest distances
    let newMinDists := dists.map (extendShortestPath G dists)
    -- ⟨true, newMinDists⟩
    -- terminate if nothing changes
    if newMinDists = dists
    then ⟨true, newMinDists⟩
    -- otherwise do another round with the new distances
    else BF_loop G newMinDists (hops - 1)

-- The Bellman-Ford algorithm, but mainly just initializes state and calls the helper
def BF (G : Graph) (source : Vertex) : Bool × PathDistances :=
  -- This just maps every vertex to none, except the source which has shortest path of dist 0
  let dists : PathDistances := G.map (fun (vert, _) => if vert = source then (vert, 0) else (vert, none))

  -- size + 1 because we want to terminate after exactly running |V| rounds
  -- Normally you'd start at 0 then go up to |V|, but switching it to this form
  -- gives us termination for free.
  BF_loop G dists (dists.length + 1)

-- End Implementation

-- These three cases show the algorithm covering the specification
-- All positive edges, shows behavior is as desired
def simplePaths := fromEdges [(1, 3, 3), (1, 2, 1), (2, 3, 1)]
#eval BF simplePaths 2
#eval BF simplePaths 3

-- -- Here's an example of it working with negative edges, in a case where Dijkstra's fails
def negEdgeShorter := fromEdges [(1, 3, 1), (1, 2, 2), (2, 3, -3)]
#eval BF simplePaths 1

-- -- Here's it detecting a negative edge cycle, note doesn't matter where you start
def negCycle := fromEdges [(1, 2, 1), (2, 3, 2), (3, 1, -4)]
#eval BF negCycle 1
#eval BF negCycle 2
#eval BF negCycle 3

-- PATH DEFINITIONS

-- -- Defintions relating to paths and shortest paths
-- inductive Path: Graph → List Edge → (u v : Vertex) → Prop
-- | path_self: ∀ G u, G.contains u → Path G [] u u
-- | path_edge: ∀ G u v, (getOutEdges G u).contains v → Path G [(u, v, (getOutEdges G u).get! v)] u v
-- | path_cons: ∀ G p x y z, Path G p y z → (getOutEdges G x).contains y → Path G ((x, y, (getOutEdges G x).get! y) :: p) x z

-- -- The weight of a path
-- def pathWeight : List Edge → Weight
-- | [] => 0
-- | (_, _, w) :: edges => w + pathWeight edges

-- -- The shortest path definition
-- def shortestPath (G : Graph) (u v : Vertex) (p : List Edge) :=
--   Path G p u v ∧ ∀ l, Path G l u v → pathWeight l <= pathWeight p

-- -- Defines the shortest k-hop path of a graph, as defined in the paper
-- -- It just makes some claim about the weight of the shortest path that exists
-- noncomputable
-- def shortestPathWeight (G : Graph) (u v : Vertex) (k : Nat) : WithTop Int :=
--   if h : ∃ (l : List Edge), shortestPath G u v l ∧ l.length ≤ k then
--     pathWeight (choose h)
--   else
--     ⊤

-- -- This is the proof of the inductive case of BF, where you look at all in-neighbors
-- -- and update the shortest path to a vertex. The proof on paper is quite simple,
-- -- but I'm struggling to work the with hashmap types to unpack the definitions
-- -- I don't know if I should try switching
-- theorem extend_hops (G : Graph) (s : Vertex) (dists : HashMap Vertex (WithTop Int))
--     (hops : Nat) (h : ∀ v, dists.getD v ⊤ = shortestPathWeight G s v hops) :
--     ∀ v, (dists.map (extendShortestPath G dists)).getD v (⊤ : WithTop Int) =
--       shortestPathWeight G s v (hops + 1) := by
--       intro v
--       simp [shortestPathWeight]
--       split_ifs with h'
--       .
--         sorry
--       . rw [HashMap.map];
--         sorry

-- -- Structure of proof of correctness for BF alg as a whole
-- theorem BF_correct (G : Graph) (s : Vertex) : ∀ (v : Vertex),
--   (BF G s).2.getD v ⊤ = shortestPathWeight G s v (G.size + 1) := by
--   intro v
--   induction G.size with
--   | zero =>
--       rw [BF, BF_loop]
--       split_ifs with h
--       . simp [shortestPathWeight]
--         sorry
--       . sorry
--   | succ n ih => sorry
