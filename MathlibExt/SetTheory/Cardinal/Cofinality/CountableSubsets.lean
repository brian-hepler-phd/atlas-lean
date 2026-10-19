/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 37, Logic 39, Logic 40, Logic 41, Logic 51

/-!
# `MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets`

## References

* Jech (for `IsClubOmega`, `IsStationaryOmega`, `ClosurePoints`, `ClosurePointsSeq`)
-/

namespace MetaMathlibExt

-- Logic 37: Countable subsets of $\alpha$

def CountableSubsets.{u} (α : Type u) : Set (Set α) := {x | x.Countable}

-- Logic 39: Club in $[X]^\omega$

/-- Source: Jech. -/
structure IsClubOmega {α : Type*} (C : Set (Set α)) : Prop where
  mem_countable : ∀ x ∈ C, x.Countable
  cofinal : ∀ x : Set α, x.Countable → ∃ y ∈ C, x ⊆ y
  closed : ∀ f : ℕ → Set α, (∀ n, f n ∈ C) → Monotone f → (⋃ n, f n) ∈ C

-- Logic 40: Stationarity in $[X]^\omega$

/-- Source: Jech. -/
def IsStationaryOmega {α : Type*} (S : Set (Set α)) : Prop :=
  ∀ ⦃C : Set (Set α)⦄, IsClubOmega C → (S ∩ C).Nonempty

-- Logic 41: Closure points

/-- Source: Jech. -/
def ClosurePoints {α : Type*} (F : Finset α → α) : Set (Set α) :=
  {x | x.Countable ∧ ∀ s : Finset α, ↑s ⊆ x → F s ∈ x}

-- Logic 51: Closure Points Sequence

/-- Source: Jech. -/
def ClosurePointsSeq {α : Type*} (F : ℕ → Finset α → α) : Set (Set α) :=
  {x | x.Countable ∧ ∀ (n : ℕ) (s : Finset α), ↑s ⊆ x → F n s ∈ x}

end MetaMathlibExt

end
