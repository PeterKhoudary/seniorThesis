import Lean
import Mathlib.Tactic

-- This file contains an efficient implementation of the priority queue (PQ) interface using leftist heaps, with proofs of correctness for each interface method.

/-
We define the PQ interface using the operations with implementation complexity as follows:
1. empty : create an empty PQ in O(1)
2. insert : insert a new (key, priority) pair into the PQ a in O(log |a|)
3. deleteMin : remove the minimum element from the PQ a in O(log |a|)
4. meld : merge PQ a and PQ b in O(log |a| + log |b|)
-/

/-
A valid leftist heap is a binary tree that satisfies the following properties:
1. The min heap property: for every node, the priority of the node is less than or equal to the priorities of all its descendants

2. The leftist property: for every node, the rank of the left child is greater than or equal to the rank of the right child where
   the rank of a node is defined as the length of the right spine of the subtree rooted at that node

For comprehensive details on leftist heaps (and their advantages over other implementations), see part XI of the CMU 15-210 course textbook by Umut Acar and Guy Blelloch
https://www.cs.cmu.edu/~15210/docs/book.pdf
-/

/-
Inductive definition of a leftist heap, where we only allow integer priorities
  Note that even though the definition of rank is recursive, we store it in the node so we don't have to recalculate it every time we need it
  We'll need this to get the desired time bounds on the operations
-/
inductive leftistHeap (β : Type) where
| leaf
| node (left : leftistHeap β) (key : β) (priority : Int) (rank : Nat) (right : leftistHeap β)
deriving Repr

namespace leftistHeap

-- Leftist heap internal methods
def rank {β : Type} : leftistHeap β → Nat
  | leaf => 0
  | node _ _ _ r _ => r

def singleton {β : Type} (key : β) (priority : Int) : leftistHeap β :=
  node leaf key priority 1 leaf

/-
Given two leftist heaps a b, and a key and priority, creates a new leftist heap such that the leftist property is preserved locally
That is, it sets the one with greater rank as the left child and updates rank accordingly
-/
def mkLeftistNode {β : Type} (left : leftistHeap β) (key : β) (priority : Int) (right : leftistHeap β) : leftistHeap β :=
  if rank left < rank right
  then node right key priority (rank left + 1) left
  else node left key priority (rank right + 1) right

-- PQ INTERFACE METHODS
def empty (β : Type) : leftistHeap β := leaf

/-
Merges two leftist heaps such that they maintain their validity.
Observe that we only ever recurse along the right spine of a given heap, and
since we do constant work locally, this is O(rank a + rank b).

We'll show later that given an arbitrary valid leftist heap h, O(rank h) = O(log |h|).
Therefore this operation is O(log |a| + log |b|).
-/
def meld {β : Type} : leftistHeap β → leftistHeap β → leftistHeap β
  | leaf, b => b
  | a, leaf => a
  | node la ka pa rka ra, node lb kb pb rkb rb =>
    if pa < pb
    then mkLeftistNode la ka pa (meld ra (node lb kb pb rkb rb))
    else mkLeftistNode lb kb pb (meld (node la ka pa rka ra) rb)

/-
Inserts a new (key, priority) pair into the heap by using meld
This is O(log |h|), as we take the time bounds from meld
-/
def insert {β : Type} (h : leftistHeap β) (key : β) (priority : Int) : leftistHeap β :=
  meld h (singleton key priority)

/-
Returns the minimum element of the heap and the new heap after removing it
This is O(log |h|), as we take the time bounds from meld where each subheap has rank upper bounded by the rank of the original heap
-/
def deleteMin {β : Type} (h : leftistHeap β) : Option (β × Int) × leftistHeap β :=
  match h with
  | leaf => (none, h)
  | node left key priority _ right => ((key, priority), meld left right)

-- VALIDITY PREDICATES

-- A heap is a forAllHeap if some property holds for all nodes in the heap
inductive forAllHeap {β : Type} (p : β → Int → Prop) : leftistHeap β → Prop
| leaf : forAllHeap p leaf
| node left key priority rank right :
    p key priority → -- the property holds locally
    forAllHeap p left → -- the property holds for all nodes in the left subheap
    forAllHeap p right → -- the property holds for all nodes in the right subheap
    forAllHeap p (node left key priority rank right)

-- A heap is a min heap if at every node, the priority of the node is less than or equal to the priority of its children
inductive minHeap {β : Type} : leftistHeap β → Prop
| leaf : minHeap leaf
| node left key priority rank right:
    forAllHeap (fun _ pL => priority ≤ pL) left → -- all nodes in left subheap have priority greater than or equal to the node
    forAllHeap (fun _ pR => priority ≤ pR) right → -- all nodes in right subheap have priority greater than or equal to the node
    minHeap left → -- property also holds for left subheap
    minHeap right → -- property also holds for right subheap
    minHeap (node left key priority rank right)

-- A heap satisfies the leftist property if for every node, the rank of the left child is greater than or equal to the rank of the right child
inductive leftistProperty {β : Type} : leftistHeap β → Prop
| leaf : leftistProperty leaf
| node left key priority rk right :
    rank right ≤ rank left → -- property holds for my direct children
    leftistProperty left → -- property holds for the left subheap
    leftistProperty right → -- property holds for the right subheap
    leftistProperty (node left key priority rk right)

-- Finally, we define a leftist heap as valid if it satisfies the min heap property and the leftist property
def validLeftistHeap {β : Type} (h : leftistHeap β) := minHeap h ∧ leftistProperty h

-- PROOF OF CORRECTNESS PART 1 : ALL OPERATIONS PRESERVE THE VALID LEFTIST HEAP PROPERTY
/-
Observe that an empty heap is trivially valid. Since all PQs would only be built
from applying meld, insert, and deleteMin to an intially empty PQ, we need to show
that these operations preserve the validity of the heaps they operate on to show
that our overall implementation is correct.

Furthermore, since we implement deleteMin and insert using meld, it suffices to show
that meld is correct, then we trivially can show that insert and deleteMin are correct.
-/

-- ForAllHeap helper lemmas
lemma parentPredicate : ∀ (β : Type) (p : β → Int → Prop) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  forAllHeap p (node left key priority rank right) → p key priority := by
    intro β p left right key priority rank h
    rcases h with ⟨h1, h2, h3⟩
    trivial

lemma leftForAllHeap : ∀ (β : Type) (p : β → Int → Prop) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  forAllHeap p (node left key priority rank right) → forAllHeap p left := by
    intro β p left right key priority rank h
    rcases h with ⟨h1, h2, h3⟩
    trivial

lemma rightForAllHeap : ∀ (β : Type) (p : β → Int → Prop) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  forAllHeap p (node left key priority rank right) → forAllHeap p right := by
    intro β p left right key priority rank h
    rcases h with ⟨h1, h2, h3⟩
    trivial

lemma leftLessThanHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority localPriority newPriority : Int) (rank : Nat),
  forAllHeap (fun _ p => priority ≤ p) (node left key localPriority rank right) → newPriority ≤ priority → forAllHeap (fun _ pL => newPriority ≤ pL) left := by
  intro β left right key priority localPriority newPriority rank h hPP
  induction left with
  | leaf => apply forAllHeap.leaf
  | node lLeft lKey lPriority lRank lRight ihL ihR =>
      have lol : forAllHeap (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) :=
          leftForAllHeap β (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) right key localPriority rank h
      have lol' : priority ≤ lPriority := parentPredicate β _ lLeft lRight lKey lPriority lRank lol
      apply forAllHeap.node
      . apply le_trans
        . apply hPP
        . apply lol'
      . apply ihL
        . apply forAllHeap.node
          . apply parentPredicate β (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) right key localPriority rank h
          . apply leftForAllHeap β (fun _ pL => priority ≤ pL) lLeft lRight lKey lPriority lRank lol
          . exact rightForAllHeap β (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) right key localPriority rank h
      . apply ihR
        . apply forAllHeap.node
          . apply parentPredicate β (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) right key localPriority rank h
          . exact rightForAllHeap β (fun _ pL => priority ≤ pL) lLeft lRight lKey lPriority lRank lol
          . exact rightForAllHeap β (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) right key localPriority rank h

lemma rightLessThanHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority localPriority newPriority : Int) (rank : Nat),
  forAllHeap (fun _ p => priority ≤ p) (node left key localPriority rank right) → newPriority ≤ priority → forAllHeap (fun _ pL => newPriority ≤ pL) right := by
  intro β left right key priority localPriority newPriority rank h hPP
  induction right with
  | leaf => apply forAllHeap.leaf
  | node rLeft rKey rPriority rRank rRight ihL ihR =>
      have lol : forAllHeap (fun _ pR => priority ≤ pR) (node rLeft rKey rPriority rRank rRight) :=
          rightForAllHeap β (fun _ pR => priority ≤ pR) left (node rLeft rKey rPriority rRank rRight) key localPriority rank h
      have lol' : priority ≤ rPriority := parentPredicate β _ rLeft rRight rKey rPriority rRank lol
      apply forAllHeap.node
      . apply le_trans
        . apply hPP
        . apply lol'
      . apply ihL
        . apply forAllHeap.node
          . apply parentPredicate β (fun _ pL => priority ≤ pL) left (node rLeft rKey rPriority rRank rRight) key localPriority rank h
          . exact leftForAllHeap β (fun _ pR => priority ≤ pR) left (node rLeft rKey rPriority rRank rRight) key localPriority rank h
          . exact leftForAllHeap β (fun _ pR => priority ≤ pR) rLeft rRight rKey rPriority rRank lol
      . apply ihR
        . apply forAllHeap.node
          . apply parentPredicate β (fun _ pL => priority ≤ pL) left (node rLeft rKey rPriority rRank rRight) key localPriority rank h
          . exact leftForAllHeap β (fun _ pR => priority ≤ pR) left (node rLeft rKey rPriority rRank rRight) key localPriority rank h
          . exact rightForAllHeap β (fun _ pR => priority ≤ pR) rLeft rRight rKey rPriority rRank lol

def mkLeftistForAll : ∀ (β : Type) (p : β → Int → Prop) (left right : leftistHeap β) (key : β) (priority : Int),
  forAllHeap p (mkLeftistNode left key priority right) →
  forAllHeap p left ∧ forAllHeap p right := by
    intro β p left right key priority h
    rw [mkLeftistNode] at h
    split at h
    . constructor
      . exact rightForAllHeap β p right left key priority ((left.rank) + 1) h
      . exact leftForAllHeap β p right left key priority ((left.rank) + 1) h
    . constructor
      . exact leftForAllHeap β p left right key priority ((right.rank) + 1) h
      . exact rightForAllHeap β p left right key priority ((right.rank) + 1) h

lemma smallForAllHeap : ∀ (β : Type) (oldPriority newPriority: Int) (h : leftistHeap β),
  forAllHeap (fun _ pH ↦ oldPriority ≤ pH) h → newPriority ≤ oldPriority →  forAllHeap (fun _ pH ↦ newPriority ≤ pH) h := by
  intro β oldPriority newPriority h hP hPP
  induction h with
  | leaf =>
      apply forAllHeap.leaf
  | node left key priority rank right ihL ihR =>
      apply forAllHeap.node
      . apply le_trans
        . apply hPP
        . apply parentPredicate β _ left right key priority rank hP
      . apply ihL (leftForAllHeap β (fun _ pH ↦ oldPriority ≤ pH) left right key priority rank hP)
      . apply ihR (rightForAllHeap β (fun _ pH ↦ oldPriority ≤ pH) left right key priority rank hP)

-- Minheap helper lemmas
lemma minHeapLeftForAllHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → forAllHeap (fun _ pL => priority ≤ pL) left := by
  intro β left right key priority rank h
  cases h
  trivial

lemma minHeapRightForAllHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → forAllHeap (fun _ pR => priority ≤ pR) right := by
  intro β left right key priority rank h
  cases h
  trivial

lemma leftMinHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → minHeap left := by
  intro β left right key priority rank h
  cases h
  trivial

lemma rightMinHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → minHeap right := by
  intro β left right key priority rank h
  cases h
  trivial

lemma rightLessThan : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority newPriority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → newPriority ≤ priority → forAllHeap (fun _ pR => newPriority ≤ pR) right := by
  intro β left right key priority newPriority rank h hPP
  induction right with
  | leaf => apply forAllHeap.leaf
  | node rLeft rKey rPriority rRank rRight ihL ihR =>
      apply forAllHeap.node
      . have lol : forAllHeap (fun _ pR => priority ≤ pR) (node rLeft rKey rPriority rRank rRight) := minHeapRightForAllHeap β left (node rLeft rKey rPriority rRank rRight) key priority rank h
        have lol' : priority ≤ rPriority := parentPredicate β _ rLeft rRight rKey rPriority rRank lol
        apply le_trans
        . apply hPP
        . apply lol'
      . apply ihL
        apply minHeap.node
        . apply leftForAllHeap β _ left (node rLeft rKey rPriority rRank rRight) key priority rank
          apply forAllHeap.node
          . omega
          . apply minHeapLeftForAllHeap β left (node rLeft rKey rPriority rRank rRight) key priority rank h
          . exact minHeapRightForAllHeap β left (node rLeft rKey rPriority rRank rRight) key priority rank h
        . apply leftForAllHeap β _ rLeft rRight rKey rPriority rRank
          apply minHeapRightForAllHeap β left (node rLeft rKey rPriority rRank rRight) key priority rank h
        . exact leftMinHeap β left _ key priority rank h
        . apply leftMinHeap β rLeft rRight rKey rPriority rRank
          exact rightMinHeap β left _ key priority rank h

      . apply ihR
        apply minHeap.node
        . apply leftForAllHeap β _ left (node rLeft rKey rPriority rRank rRight) key priority rank
          apply forAllHeap.node
          . omega
          . apply minHeapLeftForAllHeap β left (node rLeft rKey rPriority rRank rRight) key priority rank h
          . exact minHeapRightForAllHeap β left (node rLeft rKey rPriority rRank rRight) key priority rank h
        . apply rightForAllHeap β _ rLeft rRight rKey rPriority rRank
          apply minHeapRightForAllHeap β left (node rLeft rKey rPriority rRank rRight) key priority rank h
        . exact leftMinHeap β left _ key priority rank h
        . apply rightMinHeap β rLeft rRight rKey rPriority rRank
          exact rightMinHeap β left _ key priority rank h

lemma leftLessThan : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority newPriority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → newPriority ≤ priority → forAllHeap (fun _ pL => newPriority ≤ pL) left := by
  intro β left right key priority newPriority rank h hPP
  induction left with
  | leaf => apply forAllHeap.leaf
  | node lLeft lKey lPriority lRank lRight ihL ihR =>
      apply forAllHeap.node
      . have lol : forAllHeap (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) := minHeapLeftForAllHeap β (node lLeft lKey lPriority lRank lRight) right key priority rank h
        have lol' : priority ≤ lPriority := parentPredicate β _ lLeft lRight lKey lPriority lRank lol
        apply le_trans
        . apply hPP
        . apply lol'
      . apply ihL
        apply minHeap.node
        . apply leftForAllHeap β _ lLeft lRight lKey lPriority lRank
          exact minHeapLeftForAllHeap β (node lLeft lKey lPriority lRank lRight) right key priority rank h
        . exact minHeapRightForAllHeap β (node lLeft lKey lPriority lRank lRight) right key priority rank h
        . apply leftMinHeap β lLeft lRight lKey lPriority lRank
          exact leftMinHeap β (node lLeft lKey lPriority lRank lRight) right key priority rank h
        . exact rightMinHeap β (node lLeft lKey lPriority lRank lRight) right key priority rank h


      . apply ihR
        apply minHeap.node
        . apply rightForAllHeap β _ lLeft lRight lKey lPriority lRank
          exact minHeapLeftForAllHeap β (node lLeft lKey lPriority lRank lRight) right key priority rank h
        . exact minHeapRightForAllHeap β (node lLeft lKey lPriority lRank lRight) right key priority rank h
        . apply rightMinHeap β lLeft lRight lKey lPriority lRank
          exact leftMinHeap β (node lLeft lKey lPriority lRank lRight) right key priority rank h
        . exact rightMinHeap β (node lLeft lKey lPriority lRank lRight) right key priority rank h

lemma singleton_minHeap : ∀ (β : Type) (key : β) (priority : Int),
  minHeap (singleton key priority) := by
  intro β key priority
  rw [singleton]
  apply minHeap.node
  . exact forAllHeap.leaf
  . exact forAllHeap.leaf
  . apply minHeap.leaf
  . apply minHeap.leaf

lemma mkLeftistMinHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int),
  minHeap (mkLeftistNode left key priority right) → minHeap left ∧ minHeap right := by
  intro β left right key priority h
  rw [mkLeftistNode] at h
  split at h
  . constructor
    . exact rightMinHeap β right left key priority ((left.rank) + 1) h
    . exact leftMinHeap β right left key priority ((left.rank) + 1) h
  . constructor
    . exact leftMinHeap β left right key priority ((right.rank) + 1) h
    . exact rightMinHeap β left right key priority ((right.rank) + 1) h

lemma minHeapForAllHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → forAllHeap (fun _ pH ↦ priority ≤ pH) (node left key priority rank right) := by
  intro β left right key priority rank h
  apply forAllHeap.node
  . trivial
  . apply minHeapLeftForAllHeap β left right key priority rank h
  . apply minHeapRightForAllHeap β left right key priority rank h

-- Leftist property helper lemmas
lemma singleton_leftistProperty : ∀ (β : Type) (key : β) (priority : Int),
  leftistProperty (singleton key priority) := by
  intro β key priority
  apply leftistProperty.node
  . trivial
  . exact leftistProperty.leaf
  . exact leftistProperty.leaf

lemma rightLeftistProperty : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rk : ℕ),
  leftistProperty (node left key priority rk right) → leftistProperty right := by
  intro β left right key priority rk h
  cases h
  trivial

lemma leftLeftistProperty : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rk : ℕ),
  leftistProperty (node left key priority rk right) → leftistProperty left := by
  intro β left right key priority rk h
  cases h
  trivial

lemma mkLeftistLeftistProperty : ∀ (β : Type) (a b : leftistHeap β) (key : β) (priority : Int),
  leftistProperty a ∧ leftistProperty b ↔ leftistProperty (mkLeftistNode a key priority b) := by
  intro β a b key priority
  constructor
  . intro h
    rcases h with ⟨hA, hB⟩
    rw [mkLeftistNode]
    split_ifs with hRank
    . apply leftistProperty.node
      . exact le_of_lt hRank
      . exact hB
      . exact hA
    . apply leftistProperty.node
      . rw [not_lt] at hRank
        exact hRank
      . exact hA
      . exact hB
  . intro h
    rw [mkLeftistNode] at h
    split at h
    . constructor
      . exact rightLeftistProperty β b a key priority ((a.rank) + 1) h
      . exact leftLeftistProperty β b a key priority ((a.rank) + 1) h
    . constructor
      . exact leftLeftistProperty β a b key priority ((b.rank) + 1) h
      . exact rightLeftistProperty β a b key priority ((b.rank) + 1) h

-- Validity helper lemmas
lemma validMinHeap {β : Type} (h : leftistHeap β) : validLeftistHeap h → minHeap h := by
  intro h'
  exact h'.left

lemma validLeftistProperty {β : Type} (h : leftistHeap β) : validLeftistHeap h → leftistProperty h := by
  intro h'
  exact h'.right

lemma validLeft {β : Type} (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat) :
  validLeftistHeap (node left key priority rank right) → validLeftistHeap left := by
  intro h
  rcases h with ⟨h1, h2⟩
  have leftistLeft : leftistProperty left := by
    rcases h2 with ⟨h3, h4, h5⟩
    trivial

  have minLeft : minHeap left := by
    rcases h1 with ⟨h6, h7, h8, h9⟩
    trivial

  exact ⟨minLeft, leftistLeft⟩

lemma validRight {β : Type} (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat) :
  validLeftistHeap (node left key priority rank right) → validLeftistHeap right := by
  intro h
  rcases h with ⟨h1, h2⟩
  have leftistRight : leftistProperty right := by
    rcases h2 with ⟨h3, h4, h5⟩
    trivial

  have minRight : minHeap right := by
    rcases h1 with ⟨h6, h7, h8, h9⟩
    trivial

  exact ⟨minRight, leftistRight⟩

lemma singleton_valid {β : Type} (key : β) (priority : Int) :
  validLeftistHeap (singleton key priority) := by
  rw [validLeftistHeap, singleton]
  constructor
  . apply minHeap.node
    . exact forAllHeap.leaf
    . exact forAllHeap.leaf
    . apply minHeap.leaf
    . apply minHeap.leaf
  . exact singleton_leftistProperty _ key priority

-- To prove that meld maintains the min heap property, we need the subproof below
lemma meldForAllHeap : ∀ (β : Type) (priority : Int) (a b : leftistHeap β),
  minHeap a → minHeap b →
  forAllHeap (fun _ pA ↦ priority ≤ pA) a → forAllHeap (fun _ pB ↦ priority ≤ pB) b →
  forAllHeap (fun _ pAB ↦ priority ≤ pAB) (meld a b) := by
  intro β priority a b hAmin hBmin hA hB
  induction a with
  | leaf =>
      rw [meld.eq_def]
      simp
      apply hB

  | node la ka pa rka ra ihLa ihRa =>
      induction b with
      | leaf =>
          rw [meld.eq_def]
          simp
          apply hA

      | node lb kb pb rkb rb ihLb ihRb =>
          rw [meld.eq_def]
          simp
          split_ifs with hle
          . rw [mkLeftistNode]
            split
            . apply forAllHeap.node
              . apply parentPredicate β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA
              . apply ihRa
                . apply rightMinHeap β la ra ka pa rka hAmin
                . apply rightForAllHeap β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA
              . apply leftForAllHeap β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA

            . apply forAllHeap.node
              . apply parentPredicate β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA
              . apply leftForAllHeap β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA
              . apply ihRa
                . apply rightMinHeap β la ra ka pa rka hAmin
                . apply rightForAllHeap β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA

          . rw [mkLeftistNode]
            rw [not_lt] at hle
            split
            . apply forAllHeap.node
              . apply parentPredicate β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
              . apply ihRb
                . apply rightMinHeap β lb rb kb pb rkb hBmin
                . apply rightForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
                . intro hLaMin hLa
                  have hlab : forAllHeap (fun _ pA ↦ priority ≤ pA) (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hLaMin hLa
                  have hrB : forAllHeap (fun _ pB ↦ priority ≤ pB) rb := by apply rightForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
                  rw [meld.eq_def] at hlab
                  cases la with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lla kla pla rkla rla =>
                      have lPriority : ¬ pla < pb := by
                        rw [not_lt]
                        apply le_trans
                        . apply hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lla kla pla rkla rla) := by
                            apply minHeapLeftForAllHeap β (node lla kla pla rkla rla) ra ka pa rka hAmin
                          apply parentPredicate β _ lla rla kla pla rkla lol

                      simp [lPriority] at hlab
                      have bothForAll : forAllHeap (fun _ pB ↦ priority ≤ pB) lb ∧ forAllHeap (fun _ pA ↦ priority ≤ pA) ((lla.node kla pla rkla rla).meld rb) := by
                        apply mkLeftistForAll β (fun _ pB ↦ priority ≤ pB) lb ((lla.node kla pla rkla rla).meld rb) kb pb hlab
                      exact bothForAll.right

                . intro hRaMin hRa
                  have hrab : forAllHeap (fun _ pA ↦ priority ≤ pA) (ra.meld (lb.node kb pb rkb rb)) := by apply ihRa hRaMin hRa
                  have hrB : forAllHeap (fun _ pB ↦ priority ≤ pB) rb := by apply rightForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
                  rw [meld.eq_def] at hrab
                  cases ra with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lra kra pra rkra rra =>
                      have rPriority : ¬ pra < pb := by
                        rw [not_lt]
                        apply le_trans
                        . apply hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lra kra pra rkra rra) := by
                            apply minHeapRightForAllHeap β la (node lra kra pra rkra rra) ka pa rka hAmin
                          apply parentPredicate β _ lra rra kra pra rkra lol

                      simp [rPriority] at hrab
                      have bothForAll : forAllHeap (fun _ pB ↦ priority ≤ pB) lb ∧ forAllHeap (fun _ pA ↦ priority ≤ pA) ((node lra kra pra rkra rra).meld rb) := by
                        apply mkLeftistForAll β (fun _ pB ↦ priority ≤ pB) lb ((node lra kra pra rkra rra).meld rb) kb pb hrab
                      exact bothForAll.right
              . apply leftForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB

            . apply forAllHeap.node
              . apply parentPredicate β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
              . apply leftForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
              . apply ihRb
                . apply rightMinHeap β lb rb kb pb rkb hBmin
                . apply rightForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
                . intro hLaMin hLa
                  have hlab : forAllHeap (fun _ pA ↦ priority ≤ pA) (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hLaMin hLa
                  have hrB : forAllHeap (fun _ pB ↦ priority ≤ pB) rb := by apply rightForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
                  rw [meld.eq_def] at hlab
                  cases la with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lla kla pla rkla rla =>
                      have lPriority : ¬ pla < pb := by
                        rw [not_lt]
                        apply le_trans
                        . apply hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lla kla pla rkla rla) := by
                            apply minHeapLeftForAllHeap β (node lla kla pla rkla rla) ra ka pa rka hAmin
                          apply parentPredicate β _ lla rla kla pla rkla lol
                      simp [lPriority] at hlab
                      have bothForAll : forAllHeap (fun _ pB ↦ priority ≤ pB) lb ∧ forAllHeap (fun _ pA ↦ priority ≤ pA) ((lla.node kla pla rkla rla).meld rb) := by
                        apply mkLeftistForAll β (fun _ pB ↦ priority ≤ pB) lb ((lla.node kla pla rkla rla).meld rb) kb pb hlab
                      exact bothForAll.right

                . intro hRaMin hRa
                  have hrab : forAllHeap (fun _ pA ↦ priority ≤ pA) (ra.meld (lb.node kb pb rkb rb)) := by apply ihRa hRaMin hRa
                  have hrB : forAllHeap (fun _ pB ↦ priority ≤ pB) rb := by apply rightForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
                  rw [meld.eq_def] at hrab
                  cases ra with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lra kra pra rkra rra =>
                      have rPriority : ¬ pra < pb := by
                        rw [not_lt]
                        apply le_trans
                        . apply hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lra kra pra rkra rra) := by
                            apply minHeapRightForAllHeap β la (node lra kra pra rkra rra) ka pa rka hAmin
                          apply parentPredicate β _ lra rra kra pra rkra lol
                      simp [rPriority] at hrab
                      have bothForAll : forAllHeap (fun _ pB ↦ priority ≤ pB) lb ∧ forAllHeap (fun _ pA ↦ priority ≤ pA) ((node lra kra pra rkra rra).meld rb) := by
                        apply mkLeftistForAll β (fun _ pB ↦ priority ≤ pB) lb ((node lra kra pra rkra rra).meld rb) kb pb hrab
                      exact bothForAll.right

-- Proof that meld maintains the minHeap property
theorem meld_minHeap : ∀ (β : Type) (a b : leftistHeap β),
  validLeftistHeap a → validLeftistHeap b → minHeap (meld a b) := by
  intro β a b hvA hvB
  have hA : minHeap a := by apply hvA.left
  have hB : minHeap b := by apply hvB.left
  induction a with
  | leaf =>
      rw [meld.eq_def]
      simp
      exact hB

  | node la ka pa rka ra ihLa ihRa =>
      induction b with
      | leaf =>
          rw [meld.eq_def]
          simp
          exact hA

      | node lb kb pb rkb rb ihLb ihRb =>
          rw [meld.eq_def]
          simp
          split_ifs with hle
          . rw [mkLeftistNode]
            split
            . apply minHeap.node
              . apply meldForAllHeap
                . apply rightMinHeap β la ra ka pa rka hA
                . apply hB
                . apply minHeapRightForAllHeap β la ra ka pa rka hA
                . apply smallForAllHeap
                  . apply minHeapForAllHeap β lb rb kb pb rkb hB
                  . apply le_of_lt hle
              . apply minHeapLeftForAllHeap β la ra ka pa rka hA
              . apply ihRa
                . apply validRight la ra ka pa rka hvA
                . apply rightMinHeap β la ra ka pa rka hA
              . apply leftMinHeap β la ra ka pa rka hA

            . apply minHeap.node
              . apply minHeapLeftForAllHeap β la ra ka pa rka hA
              . apply meldForAllHeap
                . apply rightMinHeap β la ra ka pa rka hA
                . apply hB
                . apply minHeapRightForAllHeap β la ra ka pa rka hA
                . apply smallForAllHeap
                  . apply minHeapForAllHeap β lb rb kb pb rkb hB
                  . apply le_of_lt hle
              . apply leftMinHeap β la ra ka pa rka hA
              . apply ihRa
                . apply validRight la ra ka pa rka hvA
                . apply rightMinHeap β la ra ka pa rka hA

          . rw [mkLeftistNode]
            rw [not_lt] at hle
            split
            . apply minHeap.node
              . apply meldForAllHeap
                . apply hA
                . apply rightMinHeap β lb rb kb pb rkb hB
                . apply smallForAllHeap
                  . apply minHeapForAllHeap β la ra ka pa rka hA
                  . apply hle
                . apply minHeapRightForAllHeap β lb rb kb pb rkb hB
              . apply minHeapLeftForAllHeap β lb rb kb pb rkb hB

              . apply ihRb
                . apply validRight lb rb kb pb rkb hvB
                . apply rightMinHeap β lb rb kb pb rkb hB
                . intro hLav hLa
                  have hlab : minHeap (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hLav hLa
                  have hrB : minHeap rb := by apply rightMinHeap β lb rb kb pb rkb hB
                  rw [meld.eq_def] at hlab
                  cases la with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lla kla pla rkla rla =>
                      have lPriority : ¬ pla < pb := by
                        rw [not_lt]
                        apply le_trans
                        . apply hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lla kla pla rkla rla) := by
                            apply minHeapLeftForAllHeap β (node lla kla pla rkla rla) ra ka pa rka hA
                          apply parentPredicate β _ lla rla kla pla rkla lol
                      simp [lPriority] at hlab
                      have bothForAll : minHeap lb ∧ minHeap ((lla.node kla pla rkla rla).meld rb) := by
                        apply mkLeftistMinHeap β lb ((lla.node kla pla rkla rla).meld rb) kb pb hlab
                      exact bothForAll.right

                . intro hRav hRa
                  have hrab : minHeap (ra.meld (lb.node kb pb rkb rb)) := by apply ihRa hRav hRa
                  have hrB : minHeap rb := by apply rightMinHeap β lb rb kb pb rkb hB
                  rw [meld.eq_def] at hrab
                  cases ra with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lra kra pra rkra rra =>
                      have rPriority : ¬ pra < pb := by
                        rw [not_lt]
                        apply le_trans
                        . apply hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lra kra pra rkra rra) := by
                            apply minHeapRightForAllHeap β la (node lra kra pra rkra rra) ka pa rka hA
                          apply parentPredicate β _ lra rra kra pra rkra lol
                      simp [rPriority] at hrab
                      have bothForAll : minHeap lb ∧ minHeap ((node lra kra pra rkra rra).meld rb) := by
                        apply mkLeftistMinHeap β lb ((node lra kra pra rkra rra).meld rb) kb pb hrab
                      exact bothForAll.right

              . apply leftMinHeap β lb rb kb pb rkb hB

            . apply minHeap.node
              . apply minHeapLeftForAllHeap β lb rb kb pb rkb hB
              . apply meldForAllHeap
                . apply hA
                . apply rightMinHeap β lb rb kb pb rkb hB
                . apply smallForAllHeap
                  . apply minHeapForAllHeap β la ra ka pa rka hA
                  . apply hle
                . apply minHeapRightForAllHeap β lb rb kb pb rkb hB
              . apply leftMinHeap β lb rb kb pb rkb hB
              . apply ihRb
                . apply validRight lb rb kb pb rkb hvB
                . apply rightMinHeap β lb rb kb pb rkb hB
                . intro hLav hLa
                  have hlab : minHeap (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hLav hLa
                  have hrB : minHeap rb := by apply rightMinHeap β lb rb kb pb rkb hB
                  rw [meld.eq_def] at hlab
                  cases la with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lla kla pla rkla rla =>
                      have lPriority : ¬ pla < pb := by
                        rw [not_lt]
                        apply le_trans
                        . apply hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lla kla pla rkla rla) := by
                            apply minHeapLeftForAllHeap β (node lla kla pla rkla rla) ra ka pa rka hA
                          apply parentPredicate β _ lla rla kla pla rkla lol
                      simp [lPriority] at hlab
                      have bothForAll : minHeap lb ∧ minHeap ((lla.node kla pla rkla rla).meld rb) := by
                        apply mkLeftistMinHeap β lb ((lla.node kla pla rkla rla).meld rb) kb pb hlab
                      exact bothForAll.right

                . intro hRav hRa
                  have hrab : minHeap (ra.meld (lb.node kb pb rkb rb)) := by apply ihRa hRav hRa
                  have hrB : minHeap rb := by apply rightMinHeap β lb rb kb pb rkb hB
                  rw [meld.eq_def] at hrab
                  cases ra with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lra kra pra rkra rra =>
                      have rPriority : ¬ pra < pb := by
                        rw [not_lt]
                        apply le_trans
                        . apply hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lra kra pra rkra rra) := by
                            apply minHeapRightForAllHeap β la (node lra kra pra rkra rra) ka pa rka hA
                          apply parentPredicate β _ lra rra kra pra rkra lol
                      simp [rPriority] at hrab
                      have bothForAll : minHeap lb ∧ minHeap ((node lra kra pra rkra rra).meld rb) := by
                        apply mkLeftistMinHeap β lb ((node lra kra pra rkra rra).meld rb) kb pb hrab
                      exact bothForAll.right

-- Proof meld preserves the leftist property
theorem meldLeftistProperty {β : Type} (a b : leftistHeap β) :
  validLeftistHeap a →
  validLeftistHeap b →
  leftistProperty (meld a b) := by
  intro hvA hvB
  have hA : leftistProperty a := by apply hvA.right
  have hB : leftistProperty b := by apply hvB.right
  induction a with
  | leaf =>
      rw [meld.eq_def]
      simp
      apply hB
  | node la ka pa rka ra ihLa ihRa =>
      induction b with
      | leaf =>
          rw [meld.eq_def]
          simp
          apply hA

      | node lb kb pb rkb rb ihLb ihRb =>
          have hla : leftistProperty la := by apply leftLeftistProperty β la ra ka pa rka hA
          have hra : leftistProperty ra := by apply rightLeftistProperty β la ra ka pa rka hA
          have hlb : leftistProperty lb := by apply leftLeftistProperty β lb rb kb pb rkb hB
          have hrb : leftistProperty rb := by apply rightLeftistProperty β lb rb kb pb rkb hB

          rw [meld.eq_def]
          simp
          split_ifs with hle
          . rw [mkLeftistNode]
            split_ifs with hRank
            . apply leftistProperty.node
              . exact le_of_lt hRank
              . apply ihRa
                . exact validRight la ra ka pa rka hvA
                . exact rightLeftistProperty β la ra ka pa rka hA
              . apply leftLeftistProperty β la ra ka pa rka hA
            . apply leftistProperty.node
              . rw [not_lt] at hRank
                exact hRank
              . apply leftLeftistProperty β la ra ka pa rka hA
              . apply ihRa
                . exact validRight la ra ka pa rka hvA
                . exact rightLeftistProperty β la ra ka pa rka hA

          . rw [mkLeftistNode]
            rw [not_lt] at hle
            split_ifs with hRank
            . apply leftistProperty.node
              . exact le_of_lt hRank
              . apply ihRb
                . exact validRight lb rb kb pb rkb hvB
                . exact rightLeftistProperty β lb rb kb pb rkb hB
                . intro hlav hla
                  have hlab : leftistProperty (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hlav hla
                  have hrB : leftistProperty rb := by apply rightLeftistProperty β lb rb kb pb rkb hB
                  rw [meld.eq_def] at hlab
                  cases la with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lla kla pla rkla rla =>
                      have lPriority : ¬ pla < pb := by
                        rw [not_lt]
                        apply le_trans
                        . exact hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lla kla pla rkla rla) := by
                            apply minHeapLeftForAllHeap β (node lla kla pla rkla rla) ra ka pa rka (hvA.left)
                          apply parentPredicate β _ lla rla kla pla rkla lol
                      simp [lPriority] at hlab
                      rw [← mkLeftistLeftistProperty] at hlab
                      exact hlab.right
                . intro hRav hRa
                  have hrab : leftistProperty (ra.meld (lb.node kb pb rkb rb)) := by apply ihRa hRav hRa
                  have hrB : leftistProperty rb := by apply rightLeftistProperty β lb rb kb pb rkb hB
                  rw [meld.eq_def] at hrab
                  cases ra with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lra kra pra rkra rra =>
                      have rPriority : ¬ pra < pb := by
                        rw [not_lt]
                        apply le_trans
                        . exact hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lra kra pra rkra rra) := by
                            apply minHeapRightForAllHeap β la (node lra kra pra rkra rra) ka pa rka (hvA.left)
                          apply parentPredicate β _ lra rra kra pra rkra lol
                      simp [rPriority] at hrab
                      rw [← mkLeftistLeftistProperty] at hrab
                      exact hrab.right
              . apply leftLeftistProperty β lb rb kb pb rkb hB

            . apply leftistProperty.node
              . rw [not_lt] at hRank
                exact hRank
              . exact leftLeftistProperty β lb rb kb pb rkb hB
              . apply ihRb
                . exact validRight lb rb kb pb rkb hvB
                . exact rightLeftistProperty β lb rb kb pb rkb hB
                . intro hlav hla
                  have hlab : leftistProperty (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hlav hla
                  have hrB : leftistProperty rb := by apply rightLeftistProperty β lb rb kb pb rkb hB
                  rw [meld.eq_def] at hlab
                  cases la with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lla kla pla rkla rla =>
                      have lPriority : ¬ pla < pb := by
                        rw [not_lt]
                        apply le_trans
                        . exact hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lla kla pla rkla rla) := by
                            apply minHeapLeftForAllHeap β (node lla kla pla rkla rla) ra ka pa rka (hvA.left)
                          apply parentPredicate β _ lla rla kla pla rkla lol
                      simp [lPriority] at hlab
                      rw [← mkLeftistLeftistProperty] at hlab
                      exact hlab.right
                . intro hRav hRa
                  have hrab : leftistProperty (ra.meld (lb.node kb pb rkb rb)) := by apply ihRa hRav hRa
                  have hrB : leftistProperty rb := by apply rightLeftistProperty β lb rb kb pb rkb hB
                  rw [meld.eq_def] at hrab
                  cases ra with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lra kra pra rkra rra =>
                      have rPriority : ¬ pra < pb := by
                        rw [not_lt]
                        apply le_trans
                        . exact hle
                        . have lol : forAllHeap (fun _ pL => pa ≤ pL) (node lra kra pra rkra rra) := by
                            apply minHeapRightForAllHeap β la (node lra kra pra rkra rra) ka pa rka (hvA.left)
                          apply parentPredicate β _ lra rra kra pra rkra lol
                      simp [rPriority] at hrab
                      rw [← mkLeftistLeftistProperty] at hrab
                      exact hrab.right

-- Given all these lemmas, we can now prove that the the entire interface respects validity
theorem empty_valid {β : Type} : validLeftistHeap (empty β) := by
  rw [validLeftistHeap]
  constructor
  . apply minHeap.leaf
  . apply leftistProperty.leaf

theorem meld_valid : ∀ (β : Type) (a b : leftistHeap β),
  validLeftistHeap a → validLeftistHeap b → validLeftistHeap (meld a b) := by
  intro β a b hvA hvB
  rw [validLeftistHeap]
  constructor
  . apply meld_minHeap
    . exact hvA
    . exact hvB
  . apply meldLeftistProperty
    . exact hvA
    . exact hvB

theorem insert_valid : ∀ (β : Type) (h : leftistHeap β) (key : β) (priority : Int) ,
  validLeftistHeap h → validLeftistHeap (insert h key priority) := by
  intro β h key priority hv
  rw [insert]
  apply meld_valid
  . exact hv
  . exact singleton_valid key priority

theorem deleteMin_valid : ∀ (β : Type) (a : leftistHeap β),
  validLeftistHeap a → ∀ (pair : Option (β × Int)) (a' : leftistHeap β ), (pair, a') = deleteMin a → validLeftistHeap a' := by
  intro β a h pair a' h'
  rw [deleteMin.eq_def] at h'
  cases a with
  | leaf =>
      simp at h'
      rw [h'.right, validLeftistHeap]
      constructor
      . exact minHeap.leaf
      . exact leftistProperty.leaf

  | node l k p rk r =>
      have hl : validLeftistHeap l := by apply validLeft l r k p rk h
      have hr : validLeftistHeap r := by apply validRight l r k p rk h

      simp at h'
      rw [h'.right]
      apply meld_valid
      . exact hl
      . exact hr

-- PROOF OF CORRECTNESS PART 2: COMPUTATIONAL COMPLEXITY
/-
We get the desired time bounds on all operations by arguing that for a given
valid leftist heap h , the rank of the heap is bounded by log2(size h + 1).

We show this holds, then reference the comments on all interface operations for a brief
explanation of how this gives us the desired time bounds.
-/

-- The size of a leftist heap is defined the same as the size of a binary tree
def size {β : Type} : leftistHeap β → Nat
  | leaf => 0
  | node left _ _ _ right => size left + size right + 1

/-
The rank of a heap is the length of its right spine. In our actual implementation,
we store the rank of a node in the actual heap. We do this so that way mkLeftistNode
is constant time, and that we don't have to recompute it each time, which would put us
severely out of time bounds. We define it recursively beneath as that defintion
lends itself to actually proving the rank bound, and then take as an axiom that
the this defintion is equal to the rank stored in the heap.

FOR JEREMY, I realize taking it as axiom is sketchy, but I'm not super sure
how I could show that this is the case.
-/
def recursiveRank {β : Type} : leftistHeap β → ℕ
  | leaf => 0
  | node _ _ _ _ right => 1 + recursiveRank right

axiom rankEqRecursive : ∀ (β : Type) (a : leftistHeap β), rank a = recursiveRank a

/-
Lemma that a leftist heap with rank r has size at least 2^r - 1.
This makes proving the actual bound significantly easier
-/
lemma rankEntries {β : Type} : ∀ (a : leftistHeap β),
  validLeftistHeap a → size a ≥ 2 ^ (rank a) - 1 := by
  intro a h
  induction a with
  | leaf =>
      rw [size, rankEqRecursive, recursiveRank]
      simp
  | node l k p rk r ihL ihR =>
      rw [size, rankEqRecursive , recursiveRank]
      rw [rankEqRecursive] at ihL ihR

      have ihL : size l ≥ 2 ^ (recursiveRank l) - 1 := by apply ihL (validLeft l r k p rk h)
      have ihR: size r ≥ 2 ^ (recursiveRank r) - 1 := by apply ihR (validRight l r k p rk h)

      have hvL : validLeftistHeap l := by apply validLeft l r k p rk h
      have hvR : validLeftistHeap r := by apply validRight l r k p rk h

      have hLgR : rank r ≤ rank l := by
         rcases (validLeftistProperty (node l k p rk r) h)
         trivial

      have hLgR : recursiveRank r ≤ recursiveRank l := by
        rw [← rankEqRecursive, ← rankEqRecursive]
        exact hLgR

      have hLgR : 2 ^ (recursiveRank r) - 1 ≤ 2 ^ (recursiveRank l) - 1 := by
        apply tsub_le_tsub_right
        rw [pow_le_pow_iff_right₀]
        . exact hLgR
        . trivial

      have ihL : l.size ≥ 2 ^ r.recursiveRank - 1 := by
        apply le_trans
        . exact hLgR
        . exact ihL

      have leftGe : size l + size r + 1 ≥ 2 ^ (recursiveRank r) - 1 + 2 ^ (recursiveRank r) - 1 + 1 := by
        apply add_le_add
        . norm_num
          rw [add_assoc]
          apply add_le_add
          . exact ihL
          . rw [← tsub_le_iff_right]
            exact ihR
        . trivial

      have rightGe : 2 ^ (recursiveRank r) - 1 + 2 ^ (recursiveRank r) - 1 + 1 ≥ 2 ^ (1 + r.recursiveRank) - 1 := by
        rw [add_comm 1, Nat.two_pow_succ]
        omega

      apply ge_trans
      . exact leftGe
      . exact rightGe

/-
The leftist rank lemma abuses the leftist property to show that the rank of a leftist heap
is logarithmic with respect to the number of nodes. Given that this is true, we get
desired time bounds on all operations.
-/
theorem leftistRank {β : Type} : ∀ (a : leftistHeap β),
  validLeftistHeap a → rank a ≤ Nat.log2 (size a + 1) := by
  intro a h
  rw [Nat.le_log2, ← tsub_le_iff_right]
  apply rankEntries a
  . exact h
  . rw [size.eq_def]
    split
    . simp
    . simp

end leftistHeap
