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

public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.InfinitaryCombinatorics.PartitionCalculus
public import MathlibExt.SetTheory.Ultrafilter.Ramsey

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 33

/-!
# Weakly compact cardinal

## References

* Jech (for `IsWeaklyCompact`)
-/

open Set Cardinal

namespace MetaMathlibExt

-- Logic 33: Weakly compact cardinal

/-- Source: Jech. -/
def IsWeaklyCompact (κ : Cardinal) : Prop :=
  ℵ₀ < κ ∧
  ∀ (I : Type) (_ : #I = κ) (F : Finset I → Bool),
    ∃ (H : Set I) (_ : #H = κ) (k : Bool), IsHomogeneousFor 2 F H k

end MetaMathlibExt

end
