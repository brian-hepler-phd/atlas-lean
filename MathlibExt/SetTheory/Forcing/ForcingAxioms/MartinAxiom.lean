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

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.PFilter
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 10, Logic 13, Logic 14, Logic 9

/-!
# `MathlibExt.SetTheory.Forcing.ForcingAxioms.MartinAxiom`

## References

* Kunen (for `IsCCC`, `MartinAxiom`)
* Handbook of Set Theory (for `IsSigmaCentered`, `MartinAxiomSigmaCentered`)
-/

namespace MetaMathlibExt

-- Logic 10: Countable chain condition in a partial order

/-- Source: Kunen. -/
def IsCCC (P : Type*) [PartialOrder P] : Prop :=
    ∀ A : Set P, IsAntichain (fun p q : P => ∃ r, r ≤ p ∧ r ≤ q) A → A.Countable

-- Logic 13: $\sigma$-centered posets

/-- Source: Handbook of Set Theory. -/
def IsSigmaCentered (P : Type*) [PartialOrder P] : Prop :=
  ∃ c : P → ℕ, ∀ (n : ℕ) (s : Finset P), (∀ p ∈ s, c p = n) → ∃ r : P, ∀ p ∈ s, r ≤ p

-- Logic 14: Martin's Axiom for $\sigma$-centered posets

/-- Source: Handbook of Set Theory. -/
def MartinAxiomSigmaCentered (κ : Cardinal) : Prop :=
   ∀ (P : Type*) [PartialOrder P], IsSigmaCentered P →
     ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ κ →
     ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

-- Logic 9: Martin's Axiom

/-- Source: Kunen. -/
def MartinAxiom (κ : Cardinal) : Prop :=
  ∀ (P : Type*) [PartialOrder P], IsCCC P →
    ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ κ →
    ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

end MetaMathlibExt

end
