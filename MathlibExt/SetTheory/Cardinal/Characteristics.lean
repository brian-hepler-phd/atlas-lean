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

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 361, Logic 362

/-!
# Unbounded family; Bounding number

## References

* Textbook (Jech) (for `IsUnboundedFamily`, `boundingNumber`)
-/

open Cardinal Ordinal Set Order

namespace MetaMathlibExt

-- Logic 361: Unbounded family

/-- Source: Textbook (Jech). -/
def IsUnboundedFamily (F : Set (ℕ → ℕ)) : Prop :=
  ¬ ∃ g : ℕ → ℕ, ∀ f ∈ F, f ≤ᶠ[Filter.atTop] g

-- Logic 362: Bounding number

/-- Source: Textbook (Jech). -/
noncomputable def boundingNumber : Cardinal :=
  sInf {c : Cardinal | ∃ F : Set (ℕ → ℕ), IsUnboundedFamily F ∧ #F = c}

end MetaMathlibExt

end
