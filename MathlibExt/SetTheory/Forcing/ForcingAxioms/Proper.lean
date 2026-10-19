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

public import Mathlib.Order.Defs.Unbundled
public import MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 43, Logic 44, Logic 45, Logic 46, Logic 47, Logic 48

/-!
# `MathlibExt.SetTheory.Forcing.ForcingAxioms.Proper`

## References

* Jech (for `modelConds`, `modelSets`, `IsCompatible`, `IsPredenseBelow`, `IsGenericFor`,
  `IsProperForcing`)
-/

namespace MetaMathlibExt

-- Logic 43: Conditions belonging to a model

/-- Source: Jech. -/
def modelConds {P : Type*} (M : Set (P ⊕ Set P)) : Set P := Sum.inl ⁻¹' M

-- Logic 44: Subsets belonding to a model

/-- Source: Jech. -/
def modelSets {P : Type*} (M : Set (P ⊕ Set P)) : Set (Set P) := Sum.inr ⁻¹' M

-- Logic 45: Compatibility

/-- Source: Jech. -/
def IsCompatible {P : Type*} [PartialOrder P] (p q : P) : Prop := ∃ r : P, r ≤ p ∧ r ≤ q

-- Logic 46: Predense below

/-- Source: Jech. -/
def IsPredenseBelow {P : Type*} [PartialOrder P] (A : Set P) (q : P) : Prop :=
  ∀ r ≤ q, ∃ a ∈ A, IsCompatible r a

-- Logic 47: $(M,P)$-generic condition

/-- Source: Jech. -/
def IsGenericFor {P : Type*} [PartialOrder P] (M : Set (P ⊕ Set P)) (q : P) : Prop :=
  ∀ D ∈ modelSets M, IsCoinitial D → IsPredenseBelow (D ∩ modelConds M) q

-- Logic 48: Proper Forcings

/-- Source: Jech. -/
def IsProperForcing (P : Type*) [PartialOrder P] : Prop :=
  ∃ C : Set (Set (P ⊕ Set P)), IsClubOmega C ∧
    ∀ M ∈ C, ∀ p ∈ modelConds M, ∃ q ≤ p, IsGenericFor M q

end MetaMathlibExt

end
