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

public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Grade

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 485, Combinatorics 486, Combinatorics 487, Combinatorics 488

/-!
# `MathlibExt.Combinatorics.Poset.Basic`

## References

* ec1 3.9.1 (for `moebiusAlgebraMul`)
* ec1 3.13 p 335 (for `flagFVector`, `flagHVector`)
* ec1 3.11 p 321 (for `IsHyperplaneArrangement`)
-/

namespace MetaMathlibExt

-- Combinatorics 485: Möbius Algebra Product

/-- Source: ec1 3.9.1. -/
noncomputable def moebiusAlgebraMul {L R : Type*} [Lattice L]
    [CommSemiring R] (f g : L →₀ R) : L →₀ R :=
  f.sum fun s a => g.sum fun t b =>
    Finsupp.single (s ⊓ t) (a * b)

-- Combinatorics 486: Flag f-Vector


/-- Source: ec1 3.13 p 335. -/
def flagFVector (P : Type*) [PartialOrder P] [Fintype P]
    [DecidableEq P] [DecidableLE P] [GradeMinOrder ℕ P]
    (S : Finset ℕ) : ℕ :=
  (Finset.univ.filter fun c : Finset P =>
    (∀ t ∈ c, grade ℕ t ∈ S) ∧
      (∀ x ∈ c, ∀ y ∈ c, x ≤ y ∨ y ≤ x) ∧
      ∀ t, grade ℕ t ∈ S → t ∉ c →
        ∃ x ∈ c, ¬(x ≤ t ∨ t ≤ x)).card

-- Combinatorics 487: Flag h-Vector


/-- Source: ec1 3.13 p 335. -/
def flagHVector (P : Type*) [PartialOrder P] [Fintype P]
    [DecidableEq P] [DecidableLE P] [GradeMinOrder ℕ P]
    (S : Finset ℕ) : ℤ :=
  ∑ T ∈ S.powerset, (-1) ^ (S \ T).card * (flagFVector P T : ℤ)

-- Combinatorics 488: Hyperplane Arrangement


/-- Source: ec1 3.11 p 321. -/
def IsHyperplaneArrangement {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : AffineSubspace K V) (A : Set (AffineSubspace K V)) :
    Prop :=
  A.Finite ∧ ∀ H ∈ A, H ≤ E ∧ (H : Set V).Nonempty ∧
    Module.finrank K H.direction + 1 =
      Module.finrank K E.direction

end MetaMathlibExt

end
