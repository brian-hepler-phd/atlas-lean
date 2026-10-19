/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang, Steven Warner
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.Tree.Aronszajn
public import MathlibExt.SetTheory.Tree.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 24, Logic 19

/-!
# $\kappa$-Suslin tree; Suslin tree

## References

* Kunen (for `IsSuslinTreeAt`)
* Jech (for `IsSuslinTree`)
-/

open Cardinal

namespace MetaMathlibExt

-- Logic 24: $\kappa$-Suslin tree

/-- Same comment as above. $\kappa$-Suslin trees don't behave well at singular $\kappa$.

Source: Kunen.
-/
def IsSuslinTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsAronszajnTreeAt κ α ∧ ∀ A : Set α, IsAntichain (· ≤ ·) A → #A < κ

-- Logic 19: Suslin tree

/-- Source: Jech. -/
def IsSuslinTree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  IsSuslinTreeAt (aleph 1) α

end MetaMathlibExt

end
