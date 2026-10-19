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

public import Mathlib.Order.Filter.CardinalInter
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 50

/-!
# Measurable cardinal

## References

* Jech (for `IsMeasurable`)
-/

open Set Cardinal Filter

namespace MetaMathlibExt

-- Logic 50: Measurable cardinal

/-- Source: Jech. -/
def IsMeasurable.{u} (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧
  ∃ (I : Type u) (_ : #I = κ) (U : Ultrafilter I),
    CardinalInterFilter (U : Filter I) κ ∧ (U : Filter I) ≤ Filter.cofinite

end MetaMathlibExt

end
