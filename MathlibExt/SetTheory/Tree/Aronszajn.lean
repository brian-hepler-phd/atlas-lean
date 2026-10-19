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
public import MathlibExt.SetTheory.Tree.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 23, Logic 12, Logic 8

/-!
# $\kappa$-Aronszajn tree; Aronszajn tree; ω₁-tree

## References

* Kunen (for `IsAronszajnTreeAt`)
* Jech (for `IsAronszajnTree`, `IsOmega1Tree`)
-/

namespace MetaMathlibExt

-- Logic 23: $\kappa$-Aronszajn tree

open Cardinal in

/-- $\kappa$-Aronszajn trees are defined in general form here, but most of the times, we are
concerned with $\kappa = \gamma^+$ for some $\gamma$. This notion doesn't behave well for singular
$\kappa$.

Source: Kunen.
-/
def IsAronszajnTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsTreeAt κ α ∧ ∀ C : Set α, IsChain (· ≤ ·) C → #C < κ

-- Logic 12: Aronszajn tree

open Cardinal in

/-- Source: Jech. -/
def IsAronszajnTree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsAronszajnTreeAt (aleph 1) α

-- Logic 8: ω₁-tree

open Cardinal in

/-- Source: Jech. -/
def IsOmega1Tree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  IsTreeAt (aleph 1 : Cardinal.{u}) α

end MetaMathlibExt

end
