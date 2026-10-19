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

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Filter.Ultrafilter.Defs

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 32

/-!
# Ramsey ultrafilter

## References

* Jech (for `IsRamseyUltrafilter`)
-/

open Set Function

namespace MetaMathlibExt

-- Logic 32: Ramsey ultrafilter

/-- Source: Jech. -/
def IsRamseyUltrafilter (U : Ultrafilter ℕ) : Prop :=
  ∀ A : ℕ → Set ℕ, Pairwise (Disjoint on A) → (⋃ n, A n) = univ → (∀ n, A n ∉ U) →
    ∃ X ∈ U, ∀ n, (X ∩ A n).Subsingleton

end MetaMathlibExt

end
