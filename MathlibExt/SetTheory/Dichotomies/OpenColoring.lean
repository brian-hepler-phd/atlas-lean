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

public import Mathlib.Topology.Bases

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 335, Logic 337, Logic 338, Logic 339

/-!
# `MathlibExt.SetTheory.Dichotomies.OpenColoring`

## References

* Jech (for `IsOpenColoring`, `IsColoringHomogeneous`, `IsColoringFree`, `OpenColoringAxiom`)
-/

namespace MetaMathlibExt

-- Logic 335: Open Coloring

/-- Source: Jech. -/
structure IsOpenColoring {X : Type} [TopologicalSpace X] (K : Set (X × X)) : Prop where
  isOpen : IsOpen K
  symm : ∀ x y : X, (x, y) ∈ K → (y, x) ∈ K
  irrefl : ∀ x : X, (x, x) ∉ K

-- Logic 337: $K$-homogeneous

/-- Source: Jech. -/
def IsColoringHomogeneous {X : Type} (K : Set (X × X)) (H : Set X) : Prop :=
  H.Pairwise fun x y => (x, y) ∈ K

-- Logic 338: $K$-free coloring

/-- Source: Jech. -/
def IsColoringFree {X : Type} (K : Set (X × X)) (H : Set X) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, (x, y) ∉ K

-- Logic 339: Open Coloring Axiom

/-- Source: Jech. -/
def OpenColoringAxiom : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] (K : Set (X × X)),
    IsOpenColoring K →
      (∃ H : Set X, ¬ H.Countable ∧ IsColoringHomogeneous K H) ∨
      (∃ F : ℕ → Set X, (⋃ n, F n) = Set.univ ∧ ∀ n, IsColoringFree K (F n))

end MetaMathlibExt

end
