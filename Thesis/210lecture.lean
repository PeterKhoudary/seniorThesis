import Lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

-- Part 1 : What is formalization, and why should I care?


-- Part 2: What is Lean, and how do I use it?

-- Lean as a proof assistant

-- First order logic
variable {α β : Type} (P Q : α → Prop) (R : α → β → Prop)

section

theorem ex1 : (∀ x, P x) ∧ (∀ x, Q x) → ∀ x, P x ∧ Q x := by
  intro h x
  -- rcases with ⟨hp, hq⟩
  constructor
  . have lol : ∀ (x : α), P x := by exact h.left
    exact lol x
  . have lol : ∀ (x : α), Q x := by exact h.right
    exact lol x

theorem ex2 : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  sorry

theorem ex3 : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y := by
  sorry

end

variable (P Q R S : Prop)

example (h1 : P ∨ Q) (h2 : P → R) : R ∨ Q := by sorry


-- this one requires classical logic!
example (h : ¬ (P ∧ Q)) : ¬ P ∨ ¬ Q := by sorry



-- More induciton

section
variable {α : Type*} [CommMonoid α]

def mypow : α → ℕ → α
  | a, 0       => 1
  | a, (n + 1) => a * (mypow a n)


theorem mypow_zero (a : α) : mypow a 0 = 1 := rfl

theorem mypow_succ (a : α) (n : ℕ) : mypow a (n + 1) = a * mypow a n := rfl

theorem mypow_add (a : α) (m n : ℕ) : mypow a (m + n) = mypow a m * mypow a n := by
  sorry

end










-- Part 3: 15-150 and 15-210 reloaded, Lean as a verifiable programming language

-- Structural induction

-- The following is an inductive definition of binary trees:
inductive BinTree where
  | empty : BinTree
  | node : BinTree → BinTree → BinTree

namespace BinTree

/-
We can define the size and the depth of a binary tree
by recursion.
-/

def size : BinTree → ℕ
  | BinTree.empty => 0
  | BinTree.node l r => size l + size r + 1

def depth : BinTree → ℕ
  | BinTree.empty => 0
  | BinTree.node l r => max (depth l) (depth r) + 1

def flip : BinTree → BinTree
  | empty => empty
  | node l r => node (flip r) (flip l)

theorem size_flip : ∀ t, size (flip t) = size t := by
  intro t
  induction t with
  | empty => rw [flip]
  | node l r ihL ihR => rw [flip, size, size, ihL, ihR]; omega

theorem depth_le_size : ∀ t : BinTree, depth t ≤ size t := by
  intro t
  induction t with
  | empty => rw [depth, size]
  | node l r ihl ihr =>
      rw [depth, size, add_le_add_iff_right]
      rcases max_cases l.depth r.depth with hl | hr
      . rw [hl.left]
        apply le_add_right
        exact ihl
      . rw [hr.left]
        apply le_add_left
        exact ihr









section
open List

-- example (f : α → β) (xs : List α) : map f (tail xs) = tail (map f xs) := by
--   induction xs with
--   | nil => rw [tail, map, tail]
--   | cons a l _ => rw [tail, map, tail]

-- You use these:
-- #check nil_append
-- #check cons_append

def snoc : List α → α → List α
  | [], y => [y]
  | (x :: xs), y => x :: snoc xs y

-- 4C. Prove this.
theorem snoc_eq_append (xs : List α) (y : α) : snoc xs y = xs ++ [y] := by
  induction xs with
  | nil => rw [snoc, nil_append]
  | cons a l ih => rw [snoc, cons_append, ih]



















-- 4D. Prove this by induction.
theorem map_snoc (f : α → β) (xs : List α) (y : α) : map f (snoc xs y) = snoc (map f xs) (f y) := by
  sorry

#check map_append

-- 4E. Prove it again without induction, using `snoc_eq_apppend` and `map_append`.
theorem map_snoc' (f : α → β) (xs : List α) (y : α) : map f (snoc xs y) = snoc (map f xs) (f y) := by
  sorry

end

-- open Finset
-- -- Proof over finite sets

-- theorem ex4 (x : ℝ) (n : ℕ) : (∑ i in range n, x^i) * (x - 1) = x^n - 1 := by
--   sorry
