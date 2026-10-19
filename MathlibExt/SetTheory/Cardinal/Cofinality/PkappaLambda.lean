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
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 55, Logic 56

/-!
# Subsets of $lambda$ of size less than $\kappa$; Club in P_κ(λ)

## References

* Jech (for `powersetCardLT`, `IsClubPowersetCardLT`)
-/

open Cardinal Ordinal

namespace MetaMathlibExt

-- Logic 55: Subsets of $lambda$ of size less than $\kappa$

/-- Source: Jech. -/
def powersetCardLT.{u} (κ lam : Cardinal.{u}) : Set (Set (Set.Iio lam.ord)) :=
  {x | #x < Cardinal.lift.{u+1} κ}

-- Logic 56: Club in P_κ(λ)

/-- Source: Jech. -/
structure IsClubPowersetCardLT.{u} (κ lam : Cardinal.{u})
    (C : Set (Set (Set.Iio lam.ord))) : Prop where
  subset : C ⊆ powersetCardLT κ lam
  cofinal : ∀ x ∈ powersetCardLT κ lam, ∃ y ∈ C, x ⊆ y
  closed : ∀ D : Set (Set (Set.Iio lam.ord)), D ⊆ C → D.Nonempty →
    #D < Cardinal.lift.{u+1} κ → DirectedOn (· ⊆ ·) D → (⋃₀ D) ∈ C

end MetaMathlibExt

end
