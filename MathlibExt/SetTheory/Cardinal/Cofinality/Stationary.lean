/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 1, Logic 42, Logic 52, Logic 53, Logic 2

/-!
# `MathlibExt.SetTheory.Cardinal.Cofinality.Stationary`

## References

* Jech (for `ContainsAllBounded`, `IsKappaCompleteIdeal`, `IsNormalIdeal`, `IsRegressive`)
-/

open Cardinal

namespace MetaMathlibExt

-- Logic 42: Contains all bounded sets

/-- Source: Jech. -/
def ContainsAllBounded.{u} (κ : Cardinal.{u}) (I : Set (Set (Set.Iio κ.ord))) : Prop :=
  ∀ X : Set (Set.Iio κ.ord),
    (∃ β : Set.Iio κ.ord, ∀ α ∈ X, (α : Ordinal) < (β : Ordinal)) → X ∈ I

-- Logic 52: $\kappa$-complete ideal

/-- Source: Jech. -/
structure IsKappaCompleteIdeal.{u} (κ : Cardinal.{u})
    (I : Set (Set (Set.Iio κ.ord))) : Prop where
  downward : ∀ X ∈ I, ∀ Y ⊆ X, Y ∈ I
  empty_mem : (∅ : Set (Set.Iio κ.ord)) ∈ I
  univ_not_mem : (Set.univ : Set (Set.Iio κ.ord)) ∉ I
  kappa_complete : ∀ F : Set (Set (Set.Iio κ.ord)),
    #F < Cardinal.lift.{u+1} κ → (∀ X ∈ F, X ∈ I) → ⋃₀ F ∈ I

-- Logic 53: Normal ideal on $\kappa$

/-- Source: Jech. -/
def IsNormalIdeal.{u} (κ : Cardinal.{u}) (I : Set (Set (Set.Iio κ.ord))) : Prop :=
  ∀ (A : Set.Iio κ.ord → Set (Set.Iio κ.ord)),
    (∀ ξ, A ξ ∈ I) →
    {α : Set.Iio κ.ord | ∃ ξ : Set.Iio κ.ord, (ξ : Ordinal) < α ∧ α ∈ A ξ} ∈ I

-- Logic 2: Regressive function

/-- The lean formalization assumes that the underlying set $S$ is a subset of a cardinal $\kappa$.
This is what is needed for Fodor's lemma, and in Set Theory in general. If we want to change this
into the more general definition where $S$ is an arbitrary set of ordinals, then a bridging Lemma
would be needed to state Fodor's Theorem, which adds an extra layer of complexity, which in my
opinion is unnecessary. I would suggest we use this definition for now, and if the more general
definition is needed in topology, for example, then we just add a new more general definition at
that time.

Source: Jech.
-/
def IsRegressive (κ : Cardinal)
    (S : Set (Set.Iio κ.ord)) (f : ↥S → Set.Iio κ.ord) : Prop :=
  ∀ x : ↥S, (x : Ordinal) ≠ 0 → (f x : Ordinal) < (x : Ordinal)

end MetaMathlibExt

end
