import Lean

inductive minLeftistHeap (β : Type) [Ord β] where
| leaf
| node (left : minLeftistHeap β) (key : β) (priority : Int) (rank : Nat) (right : minLeftistHeap β)
deriving Repr

namespace minLeftistHeap
open minLeftistHeap

def rank {β : Type} [Ord β] : minLeftistHeap β → Nat
  | leaf => 0
  | node _ _ _ r _ => r

def mkLeftistNode {β : Type} [Ord β] (left : minLeftistHeap β) (key : β) (priority : Int) (right : minLeftistHeap β) : minLeftistHeap β :=
  if rank left < rank right
  then node right key priority (rank left + 1) left
  else node left key priority (rank right + 1) right

def singleton {β : Type} [Ord β] (key : β) (priority : Int): minLeftistHeap β :=
  node leaf key priority 1 leaf

def meld {β : Type} [Ord β] : minLeftistHeap β → minLeftistHeap β → minLeftistHeap β
  | leaf, b => b
  | a, leaf => a
  | node l1 k1 p1 rk1 r1, node l2 k2 p2 rk2 r2 =>
    if p1 < p2
    then mkLeftistNode l1 k1 p1 (meld r1 (node l2 k2 p2 rk2 r2))
    else mkLeftistNode l2 k2 p2 (meld (node l1 k1 p1 rk1 r1) r2)

def insertLeftist {β : Type} [Ord β] (h : minLeftistHeap β) (key : β) (priority : Int) : minLeftistHeap β :=
  meld h (singleton key priority)


inductive forAllHeap {β : Type} [Ord β] (p : β → Int → Prop) : minLeftistHeap β → Prop
| leaf : forAllHeap p leaf
| node left key priority rank right : p key priority → forAllHeap p left → forAllHeap p right → forAllHeap p (node left key priority rank right)

inductive minHeap {β : Type} [Ord β] : minLeftistHeap β → Prop
| leaf : minHeap leaf
| node left key priority rank right:
    forAllHeap (fun _ pL => pL <= priority) left →
    forAllHeap (fun _ pR => pR <= priority) left →
    minHeap left →
    minHeap right →
    minHeap (node left key priority rank right)

structure PriorityQueue (β : Type) [Ord β] where
  heap : minLeftistHeap β
  priority : β → Int

def newPriorityQueue {β : Type} [Ord β] (priority : β → Int) : PriorityQueue β :=
  PriorityQueue.mk minLeftistHeap.leaf priority

def insertPQ {β : Type} [Ord β] (pq : PriorityQueue β) (key : β) : PriorityQueue β :=
  PriorityQueue.mk (minLeftistHeap.insertLeftist pq.heap key (pq.priority key)) pq.priority

-- def just4 := (insertPQ (newPriorityQueue (λ x => x)) 4).heap

-- theorem empty_heap_min {β : Type} [Ord β] : ∀ (p : β → Int), minHeap (newPriorityQueue p).heap := by
--   intro p
--   apply minHeap.leaf

-- theorem just4Correct : minHeap just4 := by
--   rw [just4, insertPQ, newPriorityQueue, insertLeftist, meld]
--   simp
--   rw [singleton]
--   apply minHeap.node
--   apply forAllHeap.leaf
--   apply forAllHeap.leaf
--   apply minHeap.leaf
--   apply minHeap.leaf

theorem forAllHeap_insertLeftist : ∀(β : Type) [Ord β] (p : β → Int → Prop) (h : minLeftistHeap β),
  minLeftistHeap.forAllHeap p h →
    ∀(newKey : β) (newPriority : Int), p newKey newPriority →
      minLeftistHeap.forAllHeap p (minLeftistHeap.insertLeftist h newKey newPriority) := by
  intro β Ordβ p h hP newKey newPriority pNew
  induction h with
  | leaf =>
      rw [minLeftistHeap.insertLeftist, minLeftistHeap.meld, minLeftistHeap.singleton]
      apply minLeftistHeap.forAllHeap.node
      apply pNew
      apply minLeftistHeap.forAllHeap.leaf
      apply minLeftistHeap.forAllHeap.leaf
  | node left key priority rank right ihL ihR =>
      rw [insertLeftist, meld.eq_def, singleton]
      simp
      have xH : forAllHeap p (left.node key priority rank right) → p key priority := by
            intro hAux
            cases hAux
            trivial
      have xR : forAllHeap p (left.node key priority rank right) → forAllHeap p right := by
              intro hAux
              cases hAux
              trivial
      have xL : forAllHeap p (left.node key priority rank right) → forAllHeap p left := by
              intro hAux
              cases hAux
              trivial
      split
      case isTrue hPP =>
        rw [mkLeftistNode]
        split
        case isTrue =>
          apply minLeftistHeap.forAllHeap.node
          . apply xH hP
          . rw [insertLeftist, singleton] at ihR
            apply ihR
            apply xR hP
          . apply xL hP
        case isFalse =>
          apply minLeftistHeap.forAllHeap.node
          . apply xH hP
          . apply xL hP
          . rw [insertLeftist, singleton] at ihR
            apply ihR
            apply xR hP


      case isFalse hPP =>
        rw [mkLeftistNode]
        split
        case isTrue =>
          rw [meld.eq_def]
          simp
          apply forAllHeap.node
          apply pNew
          apply hP
          exact forAllHeap.leaf
        case isFalse =>
          rw [meld.eq_def]
          simp
          apply forAllHeap.node
          apply pNew
          apply forAllHeap.leaf
          exact hP

end minLeftistHeap
