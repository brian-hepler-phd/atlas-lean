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
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import MathlibExt.SetTheory.Cardinal.Cofinality.Stationary
public import MathlibExt.SetTheory.Cardinal.LargeCardinal.Inaccessible

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 28, Logic 30

/-!
# Mahlo cardinal; Weakly Mahlo cardinal

## References

* Jech (for `IsMahlo`, `IsWeaklyMahlo`)
-/

namespace MetaMathlibExt

-- Logic 28: Mahlo cardinal

/-- Source: Jech. -/
def IsMahlo.{u} (κ : Cardinal.{u}) : Prop :=
  Cardinal.IsInaccessible κ ∧ IsStationary (inaccessibleBelow κ)

-- Logic 30: Weakly Mahlo cardinal

/-- Source: Jech. -/
def IsWeaklyMahlo.{u} (κ : Cardinal.{u}) : Prop :=
  IsWeaklyInaccessible κ ∧
  IsStationary {α : Set.Iio κ.ord | (α.val.card).IsRegular ∧ α.val.card.ord = α.val}

end MetaMathlibExt

end
