import Lean
import Mathlib.Tactic

inductive leftistHeap (β : Type) where
| leaf
| node (left : leftistHeap β) (key : β) (priority : Int) (rank : Nat) (right : leftistHeap β)
deriving Repr

namespace leftistHeap
open leftistHeap

def rank {β : Type} : leftistHeap β → Nat
  | leaf => 0
  | node _ _ _ r _ => r

def mkLeftistNode {β : Type} (left : leftistHeap β) (key : β) (priority : Int) (right : leftistHeap β) : leftistHeap β :=
  if rank left < rank right
  then node right key priority (rank left + 1) left
  else node left key priority (rank right + 1) right

def singleton {β : Type} (key : β) (priority : Int): leftistHeap β :=
  node leaf key priority 1 leaf

def meld {β : Type} : leftistHeap β → leftistHeap β → leftistHeap β
  | leaf, b => b
  | a, leaf => a
  | node la ka pa rka ra, node lb kb pb rkb rb =>
    if pa < pb
    then mkLeftistNode la ka pa (meld ra (node lb kb pb rkb rb))
    else mkLeftistNode lb kb pb (meld (node la ka pa rka ra) rb)

def insertLeftist {β : Type} (h : leftistHeap β) (key : β) (priority : Int) : leftistHeap β :=
  meld h (singleton key priority)

inductive forAllHeap {β : Type} (p : β → Int → Prop) : leftistHeap β → Prop
| leaf : forAllHeap p leaf
| node left key priority rank right :
    p key priority →
    forAllHeap p left →
    forAllHeap p right →
    forAllHeap p (node left key priority rank right)

theorem parentPredicate : ∀ (β : Type) (p : β → Int → Prop) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  forAllHeap p (node left key priority rank right) → p key priority := by
  intro β p left right key priority rank h
  rcases h with ⟨h1, h2, h3⟩
  trivial

theorem leftForAllHeap : ∀ (β : Type) (p : β → Int → Prop) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  forAllHeap p (node left key priority rank right) → forAllHeap p left := by
  intro β p left right key priority rank h
  rcases h with ⟨h1, h2, h3⟩
  trivial

theorem rightForAllHeap : ∀ (β : Type) (p : β → Int → Prop) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  forAllHeap p (node left key priority rank right) → forAllHeap p right := by
  intro β p left right key priority rank h
  rcases h with ⟨h1, h2, h3⟩
  trivial

theorem forAllHeap_insertLeftist : ∀ (β : Type) (p : β → Int → Prop) (h : leftistHeap β),
  forAllHeap p h →
    ∀(newKey : β) (newPriority : Int), p newKey newPriority →
      forAllHeap p (insertLeftist h newKey newPriority) := by

  intro β p h hP newKey newPriority pNew
  induction h with
  | leaf =>
      rw [insertLeftist, meld, singleton]
      apply forAllHeap.node
      apply pNew
      apply forAllHeap.leaf
      apply forAllHeap.leaf

  | node left key priority rank right ihL ihR =>
      rw [insertLeftist, meld.eq_def, singleton]
      simp
      split
      case isTrue hPP =>
        rw [mkLeftistNode]
        split
        case isTrue =>
          apply leftistHeap.forAllHeap.node
          . apply parentPredicate β p left right key priority rank hP
          . rw [insertLeftist, singleton] at ihR
            apply ihR
            apply rightForAllHeap β p left right key priority rank hP
          . apply leftForAllHeap β p left right key priority rank hP
        case isFalse =>
          apply leftistHeap.forAllHeap.node
          . apply parentPredicate β p left right key priority rank hP
          . apply leftForAllHeap β p left right key priority rank hP
          . rw [insertLeftist, singleton] at ihR
            apply ihR
            apply rightForAllHeap β p left right key priority rank hP

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

-- def meldForAllHeap : ∀ (β : Type) (p : β → Int → Prop) (a b : leftistHeap β), forAllHeap p a → forAllHeap p b → forAllHeap p (meld a b) := by
--   intro β p a b hA hB
--   induction a with
--   | leaf =>
--       rw [meld]
--       exact hB
--   | node la ka pa rka ra ihLa ihRa =>
--       induction b with
--       | leaf =>
--           rw [meld]
--           exact hA
--           intro _
--           trivial

--       | node lb kb pb rkb rb ihLb ihRb =>
--           rw [meld, mkLeftistNode, mkLeftistNode]
--           split
--           . split
--             . apply forAllHeap.node
--               apply parentPredicate β p la ra ka pa rka hA
--               apply ihRa
--               apply rightForAllHeap β p la ra ka pa rka hA
--               apply leftForAllHeap β p la ra ka pa rka hA

--             . apply forAllHeap.node
--               apply parentPredicate β p la ra ka pa rka hA
--               apply leftForAllHeap β p la ra ka pa rka hA
--               apply ihRa
--               apply rightForAllHeap β p la ra ka pa rka hA

--           . split
--             . apply forAllHeap.node
--               apply parentPredicate β p lb rb kb pb rkb hB
--               apply ihRb
--               apply rightForAllHeap β p lb rb kb pb rkb hB
--               sorry
--               sorry
--               sorry

--             . apply forAllHeap.node
--               apply parentPredicate β p lb rb kb pb rkb hB
--               apply leftForAllHeap β p lb rb kb pb rkb hB
--               apply ihRb
--               apply rightForAllHeap β p lb rb kb pb rkb hB
--               intro _

--               sorry

inductive minHeap {β : Type} : leftistHeap β → Prop
| leaf : minHeap leaf
| node left key priority rank right:
    forAllHeap (fun _ pL => priority ≤ pL) left →
    forAllHeap (fun _ pR => priority ≤ pR) right →
    minHeap left →
    minHeap right →
    minHeap (node left key priority rank right)

theorem rightMinHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → minHeap right := by
  intro β left right key priority rank h
  cases h
  trivial

theorem leftMinHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → minHeap left := by
  intro β left right key priority rank h
  cases h
  trivial

-- theorem rPriorityLower : ∀ (β : Type) (left rLeft rRight : leftistHeap β) (key rKey: β) (priority rPriority: Int) (rank rRank : Nat),
--   minHeap (node left key priority rank (node rLeft rKey rPriority rRank rRight)) → priority ≤ rPriority := by
--   intro β left rLeft rRight key rKey priority rPriority rank rRank h
--   cases h

--   sorry


theorem minHeapRightForAllHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → forAllHeap (fun _ pR => priority ≤ pR) right := by
  intro β left right key priority rank h
  cases h
  trivial

theorem minHeapLeftForAllHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → forAllHeap (fun _ pL => priority ≤ pL) left := by
  intro β left right key priority rank h
  cases h
  trivial

theorem rightLessThan : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority newPriority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → newPriority ≤ priority → forAllHeap (fun _ pR => newPriority ≤ pR) right := by
  intro β left right key priority newPriority rank h hPP
  induction right with
  | leaf => apply forAllHeap.leaf
  | node rLeft rKey rPriority rRank rRight ihL ihR =>
      apply forAllHeap.node
      .
        sorry
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

 theorem leftLessThan : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority newPriority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → newPriority ≤ priority → forAllHeap (fun _ pL => newPriority ≤ pL) left := by
  intro β left right key priority newPriority rank h hPP
  induction left with
  | leaf => apply forAllHeap.leaf
  | node lLeft lKey lPriority lRank lRight ihL ihR =>
      apply forAllHeap.node
      .
        sorry
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

structure PriorityQueue (β : Type) where
  heap : leftistHeap β
  priority : β → Int

def newPriorityQueue {β : Type} (priority : β → Int) : PriorityQueue β :=
  PriorityQueue.mk leftistHeap.leaf priority

def insertPQ {β : Type} (pq : PriorityQueue β) (key : β) : PriorityQueue β :=
  PriorityQueue.mk (leftistHeap.insertLeftist pq.heap key (pq.priority key)) pq.priority

def deleteMin {β : Type} (pq : PriorityQueue β) : Option (β × Int) × PriorityQueue β :=
  match pq.heap with
  | leftistHeap.leaf => ⟨none, pq⟩
  | leftistHeap.node left key priority _ right =>
    ⟨(key, priority), PriorityQueue.mk (leftistHeap.meld left right) pq.priority⟩

theorem insert_minHeap : ∀ (β : Type) (p : β → Int → Prop) (h : leftistHeap β) (newKey : β) (newPriority : Int),
  minHeap h → minHeap (insertLeftist h newKey newPriority) := by
    intro β p h newKey newPriority hP
    induction h with
    | leaf =>
        rw [insertLeftist, meld, singleton]
        apply minHeap.node
        apply forAllHeap.leaf
        apply forAllHeap.leaf
        apply minHeap.leaf
        apply minHeap.leaf

    | node left key priority rank right ihL ihR =>
        rw [insertLeftist, meld.eq_def, singleton]
        simp
        split

        case isTrue hPP =>
          rw [mkLeftistNode]
          split

          case isTrue =>
            apply minHeap.node
            . rw [insertLeftist, singleton] at ihR
              apply forAllHeap_insertLeftist _ _ _
              apply minHeapRightForAllHeap β left right key priority rank hP
              apply Int.le_of_lt hPP
            . exact minHeapLeftForAllHeap β left right key priority rank hP
            . apply ihR
              exact rightMinHeap β left right key priority rank hP
            . exact leftMinHeap β left right key priority rank hP

          case isFalse =>
            apply minHeap.node
            . apply minHeapLeftForAllHeap β left right key priority rank hP
            . rw [insertLeftist, singleton] at ihR
              apply forAllHeap_insertLeftist _ _ _
              apply minHeapRightForAllHeap β left right key priority rank hP
              apply Int.le_of_lt hPP
            . exact leftMinHeap β left right key priority rank hP
            . apply ihR
              exact rightMinHeap β left right key priority rank hP

        case isFalse hPP =>
          rw [mkLeftistNode]
          rw [Int.not_lt] at hPP
          split
          case isTrue =>
            rw [meld.eq_def]
            simp
            apply minHeap.node
            apply forAllHeap.node
            apply hPP
            apply leftLessThan β left right key priority newPriority rank hP hPP
            apply rightLessThan β left right key priority newPriority rank hP hPP
            apply forAllHeap.leaf
            apply hP
            apply minHeap.leaf
          case isFalse =>
            rw [meld.eq_def]
            simp
            apply minHeap.node
            apply forAllHeap.leaf
            apply forAllHeap.node
            apply hPP
            apply leftLessThan β left right key priority newPriority rank hP hPP
            apply rightLessThan β left right key priority newPriority rank hP hPP
            apply minHeap.leaf
            apply hP


end leftistHeap
