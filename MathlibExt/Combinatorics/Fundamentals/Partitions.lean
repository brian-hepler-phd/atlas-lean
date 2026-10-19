/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Tactic.IntervalCases

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 27, Combinatorics 28, Combinatorics 444, Combinatorics 445, Combinatorics 452, Combinatorics 460, Combinatorics 461, Combinatorics 489

/-!
# `MathlibExt.Combinatorics.Fundamentals.Partitions`

## References

* ec1 p 25 (for `WeakComposition`)
* ec1 p 45 (for `SetComposition`)
* ec1 1.8.3 (for `List.partitionConjugate`, `List.IsSelfConjugate`)
* ec1 1.7.3 (for `Nat.partitionsInBox`)
* ec1 2.5.1 (for `Nat.VPartition`)
* ec1 2.5.2 (for `List.IsUnimodal`)
* ec2 7.2 p 288 (for `Nat.Partition.Dominates`)
-/

namespace MetaMathlibExt

-- Combinatorics 27: Weak Composition

/-- Source: ec1 p 25. -/
def WeakComposition (n k : ℕ) :=
  { a : Fin k → ℕ //
    (Finset.univ : Finset (Fin k)).sum a = n
  }

-- Combinatorics 28: Ordered Set Partition

/-- Source: ec1 p 45. -/
def SetComposition {α : Type*} [DecidableEq α]
    (S : Finset α) (k : ℕ) :=
  { B : Fin k → Finset α //
    (∀ i, (B i).Nonempty) ∧
    (∀ i j, i ≠ j →
      Disjoint (B i) (B j)) ∧
    ((Finset.univ : Finset (Fin k)).biUnion B = S)
  }

-- Combinatorics 444: Conjugate Partition


/-- The operation itself is available in Mathlib as
$\mathrm{YoungDiagram.transpose}$, reached through
$\mathrm{YoungDiagram.ofRowLens}$, so this record is
largely a wrapper. It is included because conjugate
partition is standard and specific nomenclature in
enumerative combinatorics: results throughout the
subject are stated in terms of $\lambda'$, and a
definition carrying that name, at the level of the
list of parts, lets those statements be written and
read directly. The wrapper also removes a proof
obligation, since $\mathrm{ofRowLens}$ takes a
$\mathrm{List.SortedGE}$ argument while this
definition does not.

A partition is represented as the list of its parts
in weakly decreasing order with every part at least
$1$; the empty list is the empty partition. The
definition reads $\lambda_1$ off the head of the
list, so on a list that is not weakly decreasing it
does not compute a conjugate.

Source: ec1 1.8.3.
-/
def _root_.List.partitionConjugate (l : List ℕ) : List ℕ :=
  (List.range (l.head?.getD 0)).map fun j =>
    (l.filter fun p => decide (j + 1 ≤ p)).length

-- Combinatorics 445: Self-Conjugate Partition


/-- Source: ec1 1.8.3. -/
def List.IsSelfConjugate (l : List ℕ) : Prop :=
  l.partitionConjugate = l

-- Combinatorics 452: Partitions in a Box


/-- Source: ec1 1.7.3. -/
def Nat.partitionsInBox (j k n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition n =>
    Multiset.card p.parts ≤ k ∧
      ∀ x ∈ p.parts, x ≤ j).card

-- Combinatorics 460: V-Partition


/-- Source: ec1 2.5.1. -/
structure Nat.VPartition (n : ℕ) where
  corner : ℕ
  left : Multiset ℕ
  right : Multiset ℕ
  left_pos : ∀ x ∈ left, 0 < x
  right_pos : ∀ x ∈ right, 0 < x
  left_le : ∀ x ∈ left, x ≤ corner
  right_le : ∀ x ∈ right, x ≤ corner
  weight : corner + left.sum + right.sum = n

-- Combinatorics 461: Unimodal Sequence


/-- Source: ec1 2.5.2. -/
def List.IsUnimodal (d : List ℕ) : Prop :=
  (∀ x ∈ d, 0 < x) ∧
    ∃ j < d.length,
      (d.take (j + 1)).Pairwise (· ≤ ·) ∧
        (d.drop j).Pairwise (· ≥ ·)

-- Combinatorics 489: Dominance Order


/-- Source: ec2 7.2 p 288. -/
def _root_.Nat.Partition.Dominates {n : ℕ} (p q : n.Partition) : Prop :=
  ∀ i : ℕ, ((q.parts.sort (· ≥ ·)).take i).sum ≤
    ((p.parts.sort (· ≥ ·)).take i).sum

end MetaMathlibExt

end
