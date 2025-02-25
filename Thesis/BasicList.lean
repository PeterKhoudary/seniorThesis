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

-- Graph construction / manipulation functions
-- Creates an empty graph
def emptyGraph : Graph := []

-- Adds a vertex with no neighbors
def addVertex (G : Graph) (v : Vertex): Graph :=
  match G with
  | [] => [(v, [])]
  | (vert, edges) :: rest => if vert = v then G else (vert, edges) :: (addVertex rest v)

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

-- Returns the in-edges of a vertex, with the weights
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
  let newDist := inEdges.foldl (fun acc (u, w) =>
    let uPair := prevDists.find? (fun (vert, _) => vert = u)
    match uPair with
    | none => acc
    | some (_, uDist) => min  (uDist + w) acc
  ) vDist

  (v, newDist)

-- The meat of the bellman ford algorithm. Given the previous shortest path distances,
-- updates them by looking at every edge. Terminates after we've done as many rounds
-- as there vertices in the graph.
def BF_loop (G : Graph) (dists : PathDistances) (numVertices : Nat) : Bool × PathDistances  :=
  loop dists 0
  where
    loop (dists : PathDistances) (hops : Nat) : Bool × PathDistances :=
      if numVertices - hops = 0
      then (false, [])
      else
        let newMinDists := dists.map (extendShortestPath G dists)
        if newMinDists = dists
        then (true, newMinDists)
        else loop newMinDists (hops + 1)
    termination_by numVertices - hops

-- The Bellman-Ford algorithm, but mainly just initializes state and calls the helper
def BF (G : Graph) (source : Vertex) : Bool × PathDistances :=
  -- This just maps every vertex to none, except the source which has shortest path of dist 0
  let dists : PathDistances := G.map (fun (vert, _) => if vert = source then (vert, 0) else (vert, ⊤))

  BF_loop G dists G.length

-- End Implementation

-- These three cases show the algorithm covering the specification
-- All positive edges, shows behavior is as desired
def simplePaths := fromEdges [(1, 3, 3), (1, 2, 1), (2, 3, 1)]
#eval BF simplePaths 2
#eval BF simplePaths 3
#eval BF simplePaths 1

-- -- Here's an example of it working with negative edges, in a case where Dijkstra's fails
def negEdgeShorter := fromEdges [(1, 3, 1), (1, 2, 2), (2, 3, -2)]
#eval BF negEdgeShorter 1

-- -- Here's it detecting a negative edge cycle, note doesn't matter where you start
def negCycle := fromEdges [(1, 2, 1), (2, 3, 2), (3, 1, -4)]
#eval BF negCycle 1
#eval BF negCycle 2
#eval BF negCycle 3

-- PATH DEFINITIONS
-- -- Defintions relating to paths and shortest paths
inductive Path: Graph → List Edge → (u v : Vertex) → Prop
| path_self: ∀ G u, (u, _) ∈ G → Path G [] u u
| path_edge: ∀ G p u v w, Path G p u u → (v, w) ∈ (getOutEdges G u) → Path G [(u, v, w)] u v

-- -- The weight of a path
def pathWeight : List Edge → Weight
| [] => 0
| (_, _, w) :: edges => w + pathWeight edges

-- -- The shortest path definition
def shortestPath (G : Graph) (u v : Vertex) (p : List Edge) :=
  Path G p u v ∧ ∀ l, Path G l u v → pathWeight l <= pathWeight p

-- -- Defines the shortest k-hop path of a graph, as defined in the paper
-- -- It just makes some claim about the weight of the shortest path that exists
noncomputable
def shortestPathWeight (G : Graph) (u v : Vertex) (k : Nat) : WithTop Int :=
  if h : ∃ (l : List Edge), shortestPath G u v l ∧ l.length ≤ k then
    pathWeight (choose h)
  else
    ⊤

-- This is the proof of the inductive case of BF, where you look at all in-neighbors
-- and update the shortest path to a vertex.
theorem extend_hops (G : Graph) (s : Vertex) (dists : PathDistances)
    (hops : Nat) (h : ∀ v vDist, (v, vDist) ∈ dists → vDist = shortestPathWeight G s v hops) :
    ∀ v vDist, (v, vDist) ∈ (dists.map (extendShortestPath G dists)) → vDist = shortestPathWeight G s v (hops + 1) := by
  intro v vDist hIn
  rw [shortestPathWeight]
  split_ifs with h'
  . rcases h' with ⟨l, ⟨hl, hlen⟩⟩
    -- rw [choose]
    -- rw [pathWeight (choose )]

    sorry
  . rw [h v vDist]
    simp at h'
    rw [shortestPathWeight]
    split_ifs with h''
    . rcases h'' with ⟨l', ⟨hl', hlen'⟩⟩
      have negateLength := by apply h' l' hl'
      omega
    . trivial
    simp [List.map] at hIn
    -- rcases hIn with ⟨u, w, hIn⟩
    -- rcases hIn with ⟨hIn, hEx⟩
    -- simp [extendShortestPath] at hEx
    -- rcases hEx with ⟨hUv, hFold⟩
    -- simp [getInEdges, List.foldl] at hFold
    sorry

-- General proof of correctness of BF by induction on path lengths
theorem BF_correct (G : Graph) (s : Vertex): ∀ v vDist, (v, vDist) ∈ (BF G s).2 → vDist = shortestPathWeight G s v G.length := by
  intro v vDist hIn
  have h := BF G s
  induction G.length with
  | zero =>
    simp [BF] at h
    simp [BF_loop] at h
    simp [List.map] at h
    simp [shortestPathWeight] at h
    simp [List.map] at hIn
    simp [shortestPathWeight] at hIn
    trivial
  | succ n ih =>

    sorry
