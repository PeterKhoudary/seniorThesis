import Mathlib.Tactic.Linarith


-- Project 1 investigates algorithmic verification, specifically sorting algs

-- We look at insertion and merge sort here

-- This project was inspired chapter 3 of Software Foundations by Andrew Appel

-- The primary goal is to make these definitions as straightforward as possible


-- The concept of sorting first requeires the concept of permutation

inductive Permutation {A : Type* }: List A → List A -> Prop
| perm_nil: Permutation [] []
| perm_cons: ∀ a x y, Permutation x y → Permutation (a :: x) (a :: y)
| perm_swap: ∀ a b l, Permutation (a :: b :: l) (b :: a :: l)
| perm_trans: ∀ x y z, Permutation x y → Permutation y z → Permutation x z


open Permutation


-- Minor lemma which shortens later proofs

lemma perm_self {A : Type* } : ∀ (l : List A), Permutation l l := by
  intro l
  induction l with
  | nil => apply perm_nil
  | cons x xs ih => apply perm_cons; apply ih


-- We also need to define what it means for a list to be sorted

-- I decided to specialize on the integers, though you could use any type with ordering

-- This definition is much different than the Coq one in software foundations

-- However I think it's slightly more natural to think about it this way

def Sorted : List Int -> Prop
| f :: s :: t => f ≤ s ∧ Sorted (s :: t)
| _ => true


open Sorted


-- Again this will shorten later proofs

lemma sort_nil : Sorted [] := by rw [Sorted]; simp

lemma sort_tail : (∀ h t), Sorted (h :: t) → Sorted t := by
  intro hyp
  induction t with
  | nil => rw [Sorted]; simp

  | cons h' t' _ =>

      rw [Sorted] at hyp

      exact hyp.right


-- Finally we have the formal defintion of a sorting algorithm

def is_sorting_algorithm (f : List Int → List Int) :=

  ∀ l, Permutation l (f l) ∧ Sorted (f l)


--

-- INSERTION SORT

--


-- The insert algorithm for insertion, which translates really nicely in functional programming

def insert_into_sorted: Int → List Int → List Int

  | i, [] => [i]

  | i, h :: t => if i ≤ h then i :: h :: t else h :: (insert_into_sorted i t)


-- The actual insertion sort alg, which is again quite simple

def insertion_sort: List Int → List Int
  | [] => []
  | h :: t => insert_into_sorted h (insertion_sort t)


-- Proof of correctness (permutation)


-- In order to prove that insertion sort is a permutation we must first show that the insert function

-- is a permutation of a :: l, where a is the element to insert into a list

lemma perm_insert_into_sorted : ∀ a l, Permutation (a :: l) (insert_into_sorted a l) := by

  intro a l

  induction l with

  | nil => rw [insert_into_sorted]; exact perm_self [a]

  | cons h t ih =>

      rw [insert_into_sorted]

      split_ifs

      . exact perm_self (a :: h :: t)

      . have front : Permutation (h :: a :: t) (h :: insert_into_sorted a t) := by apply perm_cons _ _ _ ih

        have switch : Permutation (a :: h :: t) (h :: a :: t) := by apply perm_swap

        exact perm_trans _ _ _ switch front


-- We then get an equally simple proof of permutation

theorem perm_insertion_sort : ∀l, Permutation l (insertion_sort l) := by

  intro l

  induction l with

  | nil => rw [insertion_sort]; exact perm_nil

  | cons h t ih =>

      rw [insertion_sort]

      have front : Permutation (h :: t) (h :: insertion_sort t) := by apply perm_cons _ _ _ ih

      have inserted : Permutation (h :: insertion_sort t) (insert_into_sorted h (insertion_sort t)) := by apply perm_insert_into_sorted

      exact perm_trans _ _ _ front inserted


-- Proof of correctness (sortedness)


-- The following are helpers necessary to show that the insert function maintains sortedness

-- Just shows that there exists some "front" element after inserting an element to any list

lemma insert_nonempty : ∀ a l, ∃ h t, insert_into_sorted a l = h :: t := by

  intro a l

  induction l with

  | nil => rw [insert_into_sorted]; use a; use []

  | cons h' t' _ =>

      rw [insert_into_sorted]

      split_ifs with hyp

      . use a; use h' :: t'

      . use h';

        use insert_into_sorted a t'


-- This claims that any element in the list returned by insert is either the

-- inserted element or from the original list. This sounds like a repeat of

-- the claim of permutation for insert, but this specific format makes it

-- much easier to use in proofs

lemma insert_same_members : ∀ x a l, x ∈ insert_into_sorted a l ↔ x = a ∨ x ∈ l := by

  intro x a l

  induction l with

  | nil => simp; rw [insert_into_sorted, List.mem_singleton]

  | cons h t ih =>

      rw [insert_into_sorted]

      split_ifs with hyp

      . exact List.mem_cons

      . rw [List.mem_cons, List.mem_cons, ih, or_left_comm]



-- Claims that for any sorted list, the front of the list is ≤ all items in the list

-- I can't seem to figure out how to finish this. I looked at the built-in

-- sorting library for inspiration, but their sorted predicate is just defined as

-- as a pairwise relation, and the pairwise definition takes the lemma

-- im trying to prove here as an axiom in its definition

lemma head_sorted_min : ∀ h t, Sorted (h :: t) → ∀ x ∈ t, h ≤ x := by

  intro h t hypS x hypX

  induction t with

  | nil => contradiction

  | cons h' t' ih =>

      rw [List.mem_cons] at hypX

      rw [Sorted] at hypS

      rcases hypX with hypEq | hypMem

      . rw [hypEq]

        exact hypS.left

      . apply ih

        . -- have _ : ∀ x ∈ t', h' ≤ x := by apply head_sorted_min h' t' hypS.right

          exact hypS.right

        . apply hypMem


-- Shows that the insert function maintains the sorted invariant

-- The proof structure is complete but as you'll see in the comment I had a pretty

-- annoying error in a base case

lemma sorted_insert_into_sorted : ∀ a l, Sorted l → Sorted (insert_into_sorted a l) := by

  intro a l hyp

  induction l with

  | nil =>

      rw [insert_into_sorted, Sorted]; simp

  | cons h t ih =>

      rw [insert_into_sorted]

      split_ifs with hyp2

      . rw [Sorted]

        exact ⟨hyp2, hyp⟩

      . rw [not_le] at hyp2

        rcases insert_nonempty a t with ⟨h', t', hyp'⟩

        rw [hyp']; rw [hyp'] at ih

        rw [Sorted]

        constructor

        . have possElems : h' = a ∨ h' ∈ t := by

            induction t with

            -- This should be easy to show but I cannot get lean to acknowledge that h' = a in base case

            | nil => rw [insert_into_sorted] at hyp'; simp; rw [List.cons_eq_cons, eq_comm] at hyp'; exact hyp'.left


            | cons h'' t'' _ =>

              rw [List.mem_cons]

              rcases insert_same_members h' a (h'' :: t'') with ⟨hyp4, _⟩

              rw [List.mem_cons] at hyp4

              apply hyp4

              rw [hyp']

              exact List.mem_cons_self h' t'


          rcases possElems with hEq | hMem

          . rw [hEq]; apply le_of_lt hyp2

          . exact head_sorted_min h t hyp h' hMem


        . exact ih (sort_tail hyp)


-- Finally this gives us a super short and easy proof of the sortedness of the alg
theorem sorted_insertion_sort : ∀l, Sorted (insertion_sort l) := by
  intro l
  induction l with
  | nil => apply sort_nil
  | cons h t ih =>
      rw [insertion_sort]
      apply sorted_insert_into_sorted
      exact ih


-- Finally we can claim that insertion is in fact a sorting algorithm

theorem insertion_sort_correct : is_sorting_algorithm insertion_sort := by
  intro l
  exact ⟨perm_insertion_sort l, sorted_insertion_sort l⟩
