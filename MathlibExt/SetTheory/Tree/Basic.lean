/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner, Nam Trang
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 6, Logic 7, Logic 22, Logic 38

/-!
# `MathlibExt.SetTheory.Tree.Basic`

## References

* Jech (for `IsTree`, `level`, `IsNormalTreeAt`)
* Kunen (for `IsTreeAt`)
-/

namespace MetaMathlibExt

-- Logic 6: Tree

/-- Source: Jech. -/
def IsTree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  ∀ x : α, IsChain (· ≤ ·) {y : α | y < x}

-- Logic 7: Level of a well-founded partial ordering

/-- Source: Jech. -/
def level.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] (a : Ordinal.{u}) : Set α :=
  {x : α | WellFounded.rank (· < ·) x = a}

-- Logic 22: $\kappa$ tree

open Cardinal in

 /-- Source: Kunen. -/
 def IsTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsTree α ∧
    (∀ x : α, ∃ a < κ.ord, x ∈ level α a) ∧
    (∀ a < κ.ord, (level α a).Nonempty ∧ #(level α a) < κ)

-- Logic 38: Normal tree

/-- Source: Jech. -/
def IsNormalTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  IsTreeAt κ α ∧
  (∃ r : α, ∀ x : α, r ≤ x) ∧
  (∀ x : α, ∀ b : Ordinal.{u},
      WellFounded.rank (· < ·) x < b → b < κ.ord →
      ∃ y : α, x < y ∧ WellFounded.rank (· < ·) y = b) ∧
  (∀ x : α, ∃ y z : α, x < y ∧ x < z ∧ ¬ (y ≤ z) ∧ ¬ (z ≤ y))

end MetaMathlibExt

end
