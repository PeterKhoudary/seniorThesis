import Std.Data
open Std Option

-- I did algorithmic verification for my last project, and wanted to continue
-- The goal is write an implementation of, and prove correctness of Bellman-Ford
-- BF is a shortest path algorithm, which takes a graph (with potentially negative edges)
-- and a source, and returns the shortest path from the source to all vertices OR
-- if the graph contains a cycle with negative total weight, it reports so
-- This is desirable because shortest paths are undefined on graphs with negative cycles
-- Detailed description here: https://web.stanford.edu/class/archive/cs/cs161/cs161.1168/lecture14.pdf


-- I've written an implementation, but I  think I might've bit off more
-- than I can chew. I am really unsure how I'd start trying to prove correctness here
-- The algorithm is inductive, but getting the framework necessary to actually
-- write any inductive proof is super daunting. I started by defining the concept
-- of a valid path / shortest path, but I think for my final project I might end up pivoting
-- to implementations of different graph algs in lean

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
abbrev Graph := HashMap Vertex (HashSet (Vertex × Weight))

-- Creates an empty graph
def emptyGraph : Graph := Std.HashMap.empty

-- Adds a vertex with no neighbors
def addVertex (G : Graph) (v : Vertex): Graph := G.insertIfNew v ∅

-- This also inserts both vertices into the graph if they do not exist
def addEdge (G : Graph) (e : Edge) : Graph :=
  let (u, v, w) := e
  let neighbors := G.getD u ∅
  addVertex (G.insert u (neighbors.insert (v, w))) v

-- Creates a graph given a list of edges
def fromEdges (edges : List Edge) : Graph := edges.foldl addEdge emptyGraph

-- Helper routine, updates the shortest path distance to a neighbor given our distances from the previous round
def updateNeighborDist (vDist : Option Weight) (prevDists currDists : HashMap Vertex (Option Weight)) e :=
  let (neighbor, weight) := e
  match (vDist, prevDists.getD neighbor none) with
  | (none, _) => currDists
  | (some vDist, none) => currDists.insert neighbor (some (vDist + weight))
  | (some vDist, some neighborDist) => currDists.insert neighbor (some (min (vDist + weight) neighborDist))

-- For every neighbor we have, we update their shortest path distance and return an updated map
def updateOutNeighbors (G : Graph) (prevDists currDists : HashMap Vertex (Option Weight)) (v : Vertex) (vDist : Option Weight):=
  let neighbors := G.getD v ∅
  neighbors.fold (updateNeighborDist vDist prevDists) currDists

-- Checks if two maps are equal. I feel like I shouldn't have to write this
-- But I couldn't figure out how to get lean to be able to decide this
def mapsEq (l r : HashMap Vertex (Option Weight)) : Bool :=
  let compKeys := l.map (fun key val => val == r.getD key none)
  compKeys.fold (fun acc _ same => same && acc) true

-- The meat of the bellman ford algorithm. Given the previous shortest path distances,
-- updates them by looking at every edge. Terminates after we've done as many rounds
-- as there vertices in the graph
def BF_loop (G : Graph) (dists : HashMap Vertex (Option Weight)) (hops : Nat) :=
  if hops = 0
  -- If we're ever here, then our distances haven't converged after |V| rounds
  -- Indicating a negative cycle, so no shortest paths
  then none
  else
  -- update shortest distances
    let newMins := dists.fold (updateOutNeighbors G dists) dists
    -- terminate if nothing changes
    if mapsEq dists newMins
    then some dists
    -- otherwise do another round with the new distances
    else BF_loop G newMins (hops - 1)

-- The Bellman-Ford algorithm, but mainly just initializes state and calls the helper
def BF (G : Graph) (source : Vertex) :=
  let vertices := G.keys
  -- This just maps every vertex to none, except the source which has shortest path of dist 0
  let dists : HashMap Vertex (Option Weight) :=
    vertices.foldl
    (fun mapping v => mapping.insert v (if v = source then some 0 else none))
    HashMap.empty

  -- size + 1 because we want to terminate after exactly running |V| rounds
  -- Normally you'd start at 0 then go up to |V|, but switching it to this form
  -- gives us termination for free.
  BF_loop G dists (dists.size + 1)

-- These three cases show the algorithm covering the specification

-- All positive edges, shows behavior is as desired
def simplePaths := fromEdges [(1, 3, 3), (1, 2, 1), (2, 3, 1)]
#eval BF simplePaths 1
#eval BF simplePaths 2
#eval BF simplePaths 3

-- Here's an example of it working with negative edges, in a case where Dijkstra's fails
def negEdgeShorter := fromEdges [(1, 3, 1), (1, 2, 2), (2, 3, -3)]
#eval BF negEdgeShorter 1

-- Here's it detecting a negative edge cycle, note doesn't matter where you start
def negCycle := fromEdges [(1, 2, 1), (2, 3, 2), (3, 1, -4)]
#eval BF negCycle 1
#eval BF negCycle 2
#eval BF negCycle 3

-- Defintions relating to paths and shortest paths
inductive Path: Graph → List Edge → (u v : Vertex) → Prop
| path_self: ∀ G u, G.contains u → Path G [] u u
| path_edge: ∀ G u v w, (G.getD u ∅).contains (v, w) → Path G [(u, v, w)] u v
| path_cons: ∀ G p x y z w, Path G p y z → (G.getD x ∅).contains (y, w) → Path G ((x, y, w) :: p) x z

def pathWeight : List Edge → Weight
| [] => 0
| (_, _, w) :: edges => w + pathWeight edges

def shortestPath (G : Graph) (u v : Vertex) (p : List Edge) :=
  Path G p u v ∧ ∀ l, Path G l u v → pathWeight l <= pathWeight p
