import Lean
import Mathlib.Tactic

-- Leftist heap definition and methods
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

def deleteMinLeftist {β : Type} (h : leftistHeap β) : Option β × leftistHeap β :=
  match h with
  | leaf => (none, leaf)
  | node left key _ _ right => (key, meld left right)

-- ForAllHeap predicate and lemmas
inductive forAllHeap {β : Type} (p : β → Int → Prop) : leftistHeap β → Prop
| leaf : forAllHeap p leaf
| node left key priority rank right :
    p key priority →
    forAllHeap p left →
    forAllHeap p right →
    forAllHeap p (node left key priority rank right)

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

theorem leftLessThanHeap : ∀ (β : Type) (left right : leftistHeap β) (key : β) (priority newPriority : Int) (rank : Nat),
  forAllHeap (fun _ p => priority ≤ p) (node left key priority rank right) → newPriority ≤ priority → forAllHeap (fun _ pL => newPriority ≤ pL) left := by
  intro β left right key priority newPriority rank h hPP
  induction left with
  | leaf => apply forAllHeap.leaf
  | node lLeft lKey lPriority lRank lRight ihL ihR =>
      have lol : forAllHeap (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) :=
          leftForAllHeap β (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) right key priority rank h
      have lol' : priority ≤ lPriority := parentPredicate β _ lLeft lRight lKey lPriority lRank lol
      apply forAllHeap.node
      . apply le_trans
        . apply hPP
        . apply lol'
      . apply ihL
        . apply forAllHeap.node
          . trivial
          . apply leftForAllHeap β (fun _ pL => priority ≤ pL) lLeft lRight lKey lPriority lRank lol
          . exact rightForAllHeap β (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) right key priority rank h
      . apply ihR
        . apply forAllHeap.node
          . trivial
          . exact rightForAllHeap β (fun _ pL => priority ≤ pL) lLeft lRight lKey lPriority lRank lol
          . exact rightForAllHeap β (fun _ pL => priority ≤ pL) (node lLeft lKey lPriority lRank lRight) right key priority rank h

-- theorem forAllHeap_insertLeftist : ∀ (β : Type) (p : β → Int → Prop) (h : leftistHeap β),
  -- forAllHeap p h →
  -- ∀(newKey : β) (newPriority : Int), p newKey newPriority →
  -- forAllHeap p (insertLeftist h newKey newPriority) := by

  -- intro β p h hP newKey newPriority pNew
  -- induction h with
  -- | leaf =>
  --     rw [insertLeftist, meld, singleton]
  --     apply forAllHeap.node
  --     apply pNew
  --     apply forAllHeap.leaf
  --     apply forAllHeap.leaf

  -- | node left key priority rank right ihL ihR =>
  --     rw [insertLeftist, meld.eq_def, singleton]
  --     simp
  --     split
  --     case isTrue hPP =>
  --       rw [mkLeftistNode]
  --       split
  --       case isTrue =>
  --         apply leftistHeap.forAllHeap.node
  --         . apply parentPredicate β p left right key priority rank hP
  --         . rw [insertLeftist, singleton] at ihR
  --           apply ihR
  --           apply rightForAllHeap β p left right key priority rank hP
  --         . apply leftForAllHeap β p left right key priority rank hP
  --       case isFalse =>
  --         apply leftistHeap.forAllHeap.node
  --         . apply parentPredicate β p left right key priority rank hP
  --         . apply leftForAllHeap β p left right key priority rank hP
  --         . rw [insertLeftist, singleton] at ihR
  --           apply ihR
  --           apply rightForAllHeap β p left right key priority rank hP

  --     case isFalse hPP =>
  --       rw [mkLeftistNode]
  --       split
  --       case isTrue =>
  --         rw [meld.eq_def]
  --         simp
  --         apply forAllHeap.node
  --         apply pNew
  --         apply hP
  --         exact forAllHeap.leaf
  --       case isFalse =>
  --         rw [meld.eq_def]
  --         simp
  --         apply forAllHeap.node
  --         apply pNew
  --         apply forAllHeap.leaf
  --         exact hP

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

def meldForAllHeap : ∀ (β : Type) (priority : Int) (a b : leftistHeap β),
  forAllHeap (fun _ pA ↦ priority ≤ pA) a → forAllHeap (fun _ pB ↦ priority ≤ pB) b → forAllHeap (fun _ pAB ↦ priority ≤ pAB) (meld a b) := by
  intro β priority a b hA hB
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
            . apply forAllHeap.node
              . apply parentPredicate β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA
              . apply ihRa
                exact rightForAllHeap β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA
              . apply leftForAllHeap β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA

            . apply forAllHeap.node
              . apply parentPredicate β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA
              . apply leftForAllHeap β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA
              . apply ihRa
                exact rightForAllHeap β (fun _ pA ↦ priority ≤ pA) la ra ka pa rka hA
          . rw [mkLeftistNode]
            rw [not_lt] at hle
            split
            . apply forAllHeap.node
              . apply parentPredicate β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
              . apply ihRb
                . apply rightForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
                . intro hLa
                  have hlB : forAllHeap (fun _ pB ↦ priority ≤ pB) (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hLa
                  have hrB : forAllHeap (fun _ pB ↦ priority ≤ pB) rb := by apply rightForAllHeap β (fun _ pB ↦ priority ≤ pB) lb rb kb pb rkb hB
                  rw [meld.eq_def] at hlB
                  cases la with
                  | leaf =>
                      rw [meld.eq_def]
                      simp
                      exact hrB
                  | node lla kla pla rkla rla =>
                      have lP
                      have lPriority : ¬ pla < pb := by
                        rw [not_lt]
                        apply le_trans
                        . apply hle
                        . have lol : forAllHeap (fun _ pL ↦ pa ≤ pL) (node lla kla pla rkla rla) := by
                            apply leftForAllHeap β (fun _ pA ↦ pa ≤ pA) (node lla kla pla rkla rla) ra ka pa rka

                          apply parentPredicate β (fun _ pA ↦ pa ≤ pA) lla rla kla pla rkla lol
                      simp [lPriority] at hlB
                      have bothForAll : forAllHeap (fun _ pB ↦ priority ≤ pB) lb ∧ forAllHeap (fun _ pB ↦ priority ≤ pB) ((lla.node kla pla rkla rla).meld rb) := by
                        apply mkLeftistForAll β (fun _ pB ↦ priority ≤ pB) lb ((lla.node kla pla rkla rla).meld rb) kb pb hlB
                      exact bothForAll.right
                . sorry
              . apply leftForAllHeap β (fun _ pA ↦ priority ≤ pA) lb rb kb pb rkb hB
            . sorry

-- def meldForAllHeap : ∀ (β : Type) (p : β → Int → Prop) (a b : leftistHeap β),
--   forAllHeap p a → forAllHeap p b → forAllHeap p (meld a b) := by
--     intro β p a b hA hB
--     induction a with
--     | leaf =>
--         rw [meld.eq_def]
--         simp
--         exact hB
--     | node la ka pa rka ra ihLa ihRa =>
--         induction b with
--         | leaf =>
--             rw [meld.eq_def]
--             simp
--             exact hA
--         | node lb kb pb rkb rb ihLb ihRb =>
--             rw [meld.eq_def]
--             simp
--             split_ifs with hle
--             . rw [mkLeftistNode]
--               split
--               . apply forAllHeap.node
--                 . apply parentPredicate β p la ra ka pa rka hA
--                 . apply ihRa
--                   exact rightForAllHeap β p la ra ka pa rka hA
--                 . apply leftForAllHeap β p la ra ka pa rka hA

--               . apply forAllHeap.node
--                 . apply parentPredicate β p la ra ka pa rka hA
--                 . apply leftForAllHeap β p la ra ka pa rka hA
--                 . apply ihRa
--                   exact rightForAllHeap β p la ra ka pa rka hA

--             . rw [mkLeftistNode]
--               rw [not_lt] at hle
--               split
--               . apply forAllHeap.node
--                 . apply parentPredicate β p lb rb kb pb rkb hB
--                 . apply ihRb
--                   . apply rightForAllHeap β p lb rb kb pb rkb hB
--                   . intro hLa
--                     have hlB : forAllHeap p (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hLa
--                     have hrB : forAllHeap p rb := by apply rightForAllHeap β p lb rb kb pb rkb hB
--                     rw [meld.eq_def] at hlB
--                     cases la with
--                     | leaf =>
--                         rw [meld.eq_def]
--                         simp
--                         exact hrB
--                     | node lla kla pla rkla rla =>

--                         have lPriority : ¬ pla < pb := by
--                           rw [not_lt]
--                           apply le_trans
--                           . apply hle
--                           .
--                             sorry
--                         simp [lPriority] at hlB
--                         have bothForAll : forAllHeap p lb ∧ forAllHeap p ((lla.node kla pla rkla rla).meld rb) := by
--                           apply mkLeftistForAll β p lb ((lla.node kla pla rkla rla).meld rb) kb pb hlB
--                         exact bothForAll.right
--                   . intro hRa
--                     sorry
--                 . apply leftForAllHeap β p lb rb kb pb rkb hB
--               . apply forAllHeap.node
--                 . apply parentPredicate β p lb rb kb pb rkb hB
--                 . apply leftForAllHeap β p lb rb kb pb rkb hB
--                 . apply ihRb
--                   . apply rightForAllHeap β p lb rb kb pb rkb hB
--                   . intro hLa

--                     sorry
--                   . intro hRa
--                     sorry

-- Minheap predicate and lemmas
inductive minHeap {β : Type} : leftistHeap β → Prop
| leaf : minHeap leaf
| node left key priority rank right:
    forAllHeap (fun _ pL => priority ≤ pL) left →
    forAllHeap (fun _ pR => priority ≤ pR) right →
    minHeap left →
    minHeap right →
    minHeap (node left key priority rank right)


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

theorem meld_minHeap : ∀ (β : Type) (a b : leftistHeap β),
  minHeap a → minHeap b → minHeap (meld a b) := by
  intro β a b hA hB
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
                . apply minHeapRightForAllHeap β la ra ka pa rka hA
                . apply forAllHeap.node
                  . apply le_of_lt hle
                  . apply leftLessThan β lb rb kb pb pa rkb hB (le_of_lt hle)
                  . apply rightLessThan β lb rb kb pb pa rkb hB (le_of_lt hle)
              . apply minHeapLeftForAllHeap β la ra ka pa rka hA
              . apply ihRa (rightMinHeap β la ra ka pa rka hA)
              . apply leftMinHeap β la ra ka pa rka hA

            . apply minHeap.node
              . apply minHeapLeftForAllHeap β la ra ka pa rka hA
              . apply meldForAllHeap
                apply minHeapRightForAllHeap β la ra ka pa rka hA
                apply forAllHeap.node
                . apply le_of_lt hle
                . apply leftLessThan β lb rb kb pb pa rkb hB (le_of_lt hle)
                . apply rightLessThan β lb rb kb pb pa rkb hB (le_of_lt hle)
              . apply leftMinHeap β la ra ka pa rka hA
              . apply ihRa (rightMinHeap β la ra ka pa rka hA)

          . rw [mkLeftistNode]
            rw [not_lt] at hle
            split
            . apply minHeap.node
              . apply meldForAllHeap
                . apply forAllHeap.node
                  . apply hle
                  . apply leftLessThan β la ra ka pa pb rka hA hle
                  . apply rightLessThan β la ra ka pa pb rka hA hle
                . apply minHeapRightForAllHeap β lb rb kb pb rkb hB
              . apply minHeapLeftForAllHeap β lb rb kb pb rkb hB
              . apply ihRb
                . apply rightMinHeap β lb rb kb pb rkb hB
                . intro hLa
                  have hlab : minHeap (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hLa
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

                . intro hRa
                  have hrab : minHeap (ra.meld (lb.node kb pb rkb rb)) := by apply ihRa hRa
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
                . apply forAllHeap.node
                  . apply hle
                  . apply leftLessThan β la ra ka pa pb rka hA hle
                  . apply rightLessThan β la ra ka pa pb rka hA hle
                . apply minHeapRightForAllHeap β lb rb kb pb rkb hB
              . apply leftMinHeap β lb rb kb pb rkb hB
              . apply ihRb
                . apply rightMinHeap β lb rb kb pb rkb hB
                . intro hLa
                  have hlab : minHeap (la.meld (lb.node kb pb rkb rb)) := by apply ihLa hLa
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

                . intro hRa
                  have hrab : minHeap (ra.meld (lb.node kb pb rkb rb)) := by apply ihRa hRa
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

structure PriorityQueue (β : Type) where
  heap : leftistHeap β -- the heap structure containing the elements
  p : β → Int -- the priority function that assigns a priority to each element

def newPriorityQueue {β : Type} (p : β → Int) : PriorityQueue β :=
  PriorityQueue.mk leftistHeap.leaf p

def insertPQ {β : Type} (pq : PriorityQueue β) (key : β) : PriorityQueue β :=
  PriorityQueue.mk (leftistHeap.insertLeftist pq.heap key (pq.p key)) pq.p

def deleteMinPQ {β : Type} (pq : PriorityQueue β) : Option (β × Int) × PriorityQueue β :=
  match pq.heap with
  | leftistHeap.leaf => ⟨none, pq⟩
  | leftistHeap.node left key priority _ right =>
    ⟨(key, priority), PriorityQueue.mk (leftistHeap.meld left right) pq.p⟩

-- theorem insert_minHeap_old : ∀ (β : Type)  (h : leftistHeap β) (newKey : β) (newPriority : Int),
--   minHeap h → minHeap (insertLeftist h newKey newPriority) := by
--     intro β h newKey newPriority hP
--     induction h with
--     | leaf =>
--         rw [insertLeftist, meld, singleton]
--         apply minHeap.node
--         apply forAllHeap.leaf
--         apply forAllHeap.leaf
--         apply minHeap.leaf
--         apply minHeap.leaf

--     | node left key priority rank right ihL ihR =>
--         rw [insertLeftist, meld.eq_def, singleton]
--         simp
--         split

--         case isTrue hPP =>
--           rw [mkLeftistNode]
--           split

--           case isTrue =>
--             apply minHeap.node
--             . rw [insertLeftist, singleton] at ihR
--               apply forAllHeap_insertLeftist _ _ _
--               apply minHeapRightForAllHeap β left right key priority rank hP
--               apply Int.le_of_lt hPP
--             . exact minHeapLeftForAllHeap β left right key priority rank hP
--             . apply ihR
--               exact rightMinHeap β left right key priority rank hP
--             . exact leftMinHeap β left right key priority rank hP

--           case isFalse =>
--             apply minHeap.node
--             . apply minHeapLeftForAllHeap β left right key priority rank hP
--             . rw [insertLeftist, singleton] at ihR
--               apply forAllHeap_insertLeftist _ _ _
--               apply minHeapRightForAllHeap β left right key priority rank hP
--               apply Int.le_of_lt hPP
--             . exact leftMinHeap β left right key priority rank hP
--             . apply ihR
--               exact rightMinHeap β left right key priority rank hP

--         case isFalse hPP =>
--           rw [mkLeftistNode]
--           rw [Int.not_lt] at hPP
--           split
--           case isTrue =>
--             rw [meld.eq_def]
--             simp
--             apply minHeap.node
--             apply forAllHeap.node
--             apply hPP
--             apply leftLessThan β left right key priority newPriority rank hP hPP
--             apply rightLessThan β left right key priority newPriority rank hP hPP
--             apply forAllHeap.leaf
--             apply hP
--             apply minHeap.leaf
--           case isFalse =>
--             rw [meld.eq_def]
--             simp
--             apply minHeap.node
--             apply forAllHeap.leaf
--             apply forAllHeap.node
--             apply hPP
--             apply leftLessThan β left right key priority newPriority rank hP hPP
--             apply rightLessThan β left right key priority newPriority rank hP hPP
--             apply minHeap.leaf
--             apply hP

theorem insertLeftist_correct : ∀ (β : Type)  (h : leftistHeap β) (newKey : β) (newPriority : Int),
  minHeap h → minHeap (insertLeftist h newKey newPriority) := by
  intro β h newKey newPriority hP
  induction h with
  | leaf =>
      rw [insertLeftist, singleton]
      apply meld_minHeap
      . apply minHeap.leaf
      . apply singleton_minHeap
  | node left key priority rank right ihL ihR =>
      rw [insertLeftist]
      apply meld_minHeap
      . exact hP
      . apply singleton_minHeap

theorem deleteMin_correct : ∀ (β : Type) (pq : PriorityQueue β),
  minHeap pq.heap → ∀ (key : β) (priority : Int), pq.p key = priority → minHeap (insertLeftist pq.heap key priority) := by
  intro β pq hP key priority hKey
  rw [insertLeftist]
  apply insertLeftist_correct
  exact hP

end leftistHeap
