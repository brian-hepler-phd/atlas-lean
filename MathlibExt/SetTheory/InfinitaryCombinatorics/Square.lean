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

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 17, Logic 18

/-!
# $\Square_\kappa$ sequence; $\Square_\kappa$ sequence exists

## References

* Kunen (for `IsSquareSequence`, `Square`)
-/

namespace MetaMathlibExt

-- Logic 17: $\Square_\kappa$ sequence

/-- Source: Kunen. -/
def IsSquareSequence.{u} (κ : Cardinal.{u})
      (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType)) : Prop :=
    ∀ a : (Order.succ κ).ord.ToType, Order.IsSuccLimit a →
      (C a ⊆ Set.Iio a) ∧
      (∀ b < a, ∃ c ∈ C a, b < c) ∧
      (∀ b < a, (C a ∩ Set.Iio b).Nonempty → IsLUB (C a ∩ Set.Iio b) b → b ∈ C a) ∧
      Ordinal.type (α := ↥(C a)) (· < ·) ≤ κ.ord ∧
      (∀ b, (C a ∩ Set.Iio b).Nonempty → IsLUB (C a ∩ Set.Iio b) b →
        C b = C a ∩ Set.Iio b)

-- Logic 18: $\Square_\kappa$ sequence exists

/-- Source: Kunen. -/
def Square.{u} (κ : Cardinal.{u}) : Prop :=
    ∃ C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType), IsSquareSequence κ C

end MetaMathlibExt

end
