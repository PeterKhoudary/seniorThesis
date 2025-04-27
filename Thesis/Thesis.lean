import Lean
import Mathlib.Tactic

-- Leftist heap definition and methods
inductive leftistHeap (β : Type) where
| leaf
| node (left : leftistHeap β) (key  : β) (priority : Int) (rank : Nat) (right : leftistHeap β)
deriving Repr

namespace leftistHeap
open leftistHeap

def size {β : Type} : leftistHeap β → Nat
  | leaf => 0
  | node left _ _ _ right => size left + size right + 1

def rank {β : Type} : leftistHeap β → Nat
  | leaf => 0
  | node _ _ _ r _ => r

def depth {β : Type} : leftistHeap β → Nat
  | leaf => 0
  | node left _ _ _ right => max (depth left) (depth right) + 1

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

def deleteMinLeftist {β : Type} (h : leftistHeap β) : Option (β × Int) × leftistHeap β :=
  match h with
  | leaf => (none, leaf)
  | node left key priority _ right => ((key, priority), meld left right)

-- Predicates over leftist heaps
inductive forAllHeap {β : Type} (p : β → Int → Prop) : leftistHeap β → Prop
| leaf : forAllHeap p leaf
| node left key priority rank right :
    p key priority →
    forAllHeap p left →
    forAllHeap p right →
    forAllHeap p (node left key priority rank right)

inductive minHeap {β : Type} : leftistHeap β → Prop
| leaf : minHeap leaf
| node left key priority rank right:
    forAllHeap (fun _ pL => priority ≤ pL) left →
    forAllHeap (fun _ pR => priority ≤ pR) right →
    minHeap left →
    minHeap right →
    minHeap (node left key priority rank right)

inductive leftistProperty {β : Type} : leftistHeap β → Prop
| leaf : leftistProperty leaf
| node left key priority rk right :
    rank right ≤ rank left →
    leftistProperty left →
    leftistProperty right →
    leftistProperty (node left key priority rk right)

-- The defintion of a valid leftist heap and some lemmas
def validLeftistHeap {β : Type} (h : leftistHeap β) := minHeap h ∧ leftistProperty h

lemma validMinHeap {β : Type} (h : leftistHeap β) : validLeftistHeap h → minHeap h := fun h => h.left

lemma validLeftistProperty {β : Type} (h : leftistHeap β) : validLeftistHeap h → leftistProperty h := fun h => h.right

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

theorem leftLessThanHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority localPriority newPriority : Int) (rank : Nat),
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

theorem rightLessThanHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority localPriority newPriority : Int) (rank : Nat),
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
theorem minHeapLeftForAllHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → forAllHeap (fun _ pL => priority ≤ pL) left := by
  intro β left right key priority rank h
  cases h
  trivial

theorem minHeapRightForAllHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → forAllHeap (fun _ pR => priority ≤ pR) right := by
  intro β left right key priority rank h
  cases h
  trivial

theorem leftMinHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → minHeap left := by
  intro β left right key priority rank h
  cases h
  trivial

theorem rightMinHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority : Int) (rank : Nat),
  minHeap (node left key priority rank right) → minHeap right := by
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

theorem leftLessThan : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority newPriority : Int) (rank : Nat),
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

theorem singleton_minHeap : ∀ (β : Type) (key : β) (priority : Int),
  minHeap (singleton key priority) := by
  intro β key priority
  apply minHeap.node
  . apply forAllHeap.leaf
  . apply forAllHeap.leaf
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

-- Proof meld preserves the min heap property
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

-- Leftist property helper lemmas
lemma singleton_leftistProperty : ∀ (β : Type) (key : β) (priority : Int),
  leftistProperty (singleton key priority) := by
  intro β key priority
  apply leftistProperty.node
  . simp
  . apply leftistProperty.leaf
  . apply leftistProperty.leaf

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


-- Proof meld preserves the leftist property
theorem meldLeftist {β : Type} (a b : leftistHeap β) :
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



          -- . apply mkLeftistLeftistProperty
          --   . exact leftLeftistProperty β la ra ka pa rka hA
          --   . exact ihRa hra

          -- . apply mkLeftistLeftistProperty
          --   . exact hlb
          --   . apply ihRb
          --     . exact hrb
          --     . intro _
          --       have hlab : leftistProperty (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hla
          --       have hrB : leftistProperty rb := by apply rightLeftistProperty β lb rb kb pb rkb hB

          --       sorry
          --     . intro _
          --       sorry



-- Finally, proof that meld preserves the validity of leftist heaps
theorem meld_validLeftistHeap : ∀ (β : Type) (a b : leftistHeap β),
  validLeftistHeap a → validLeftistHeap b → validLeftistHeap (meld a b) := by
  intro β a b hvA hvB
  rw [validLeftistHeap]
  constructor
  . apply meld_minHeap
    . exact hvA
    . exact hvB
  . apply meldLeftist
    . exact hvA
    . exact hvB



-- The actual PQ structure, which is just a heap and a defined priority function
structure PriorityQueue (β : Type) where
  heap : leftistHeap β -- the heap structure containing the elements
  p : β → Int -- the priority function that assigns a priority to each element

def newPriorityQueue {β : Type} (p : β → Int) : PriorityQueue β :=
  PriorityQueue.mk leftistHeap.leaf p

def insertPQ {β : Type} (pq : PriorityQueue β) (key : β) : PriorityQueue β :=
  PriorityQueue.mk (leftistHeap.insertLeftist pq.heap key (pq.p key)) pq.p

def deleteMinPQ {β : Type} (pq : PriorityQueue β) : Option (β × Int) × PriorityQueue β :=
  let (pair, heap) := deleteMinLeftist pq.heap
  (pair, PriorityQueue.mk heap pq.p)

def meldPQ {β : Type} (pq1 pq2 : PriorityQueue β) : PriorityQueue β :=
  PriorityQueue.mk (leftistHeap.meld pq1.heap pq2.heap) pq1.p

def x := newPriorityQueue (fun x : Nat ↦ x + 1)
def y := insertPQ x 5
def z := insertPQ x 10
def a := meldPQ y z
#eval a.heap
#eval (deleteMinPQ a).snd.heap

end leftistHeap
