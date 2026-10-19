/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 2, Combinatorics 20, Combinatorics 23, Combinatorics 24, Combinatorics 429, Combinatorics 441

/-!
# `MathlibExt.Combinatorics.SimpleGraph.AlgebraicGraphTheory.Homomorphisms`

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.4, page 7. (for
  `SimpleGraph.Subgraph.IsRetract`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.2 Cores, page 104. (for
  `SimpleGraph.HasCore`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8, page 115. (for
  `SimpleGraph.IsLocalInjection`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8 Foldings and Covers, page 115. (for
  `SimpleGraph.IsLocalIsomorphism`, `SimpleGraph.Covers`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8 Foldings and Covers, page 114. (for
  `SimpleGraph.IsFolding`)
-/

open SimpleGraph

namespace MetaMathlibExt

-- Combinatorics 2: Retract

/-- Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 1.4, page 7. -/
def _root_.SimpleGraph.Subgraph.IsRetract {V : Type*} {G : SimpleGraph V}
    (H : G.Subgraph) : Prop :=
  ∃ φ : G →g H.coe, ∀ (h : H.verts), φ h.val = h

-- Combinatorics 20: Core/has core

def _root_.SimpleGraph.IsCore {V : Type*} [Fintype V] (X : SimpleGraph V) : Prop :=
  ∀ f : X →g X, Function.Bijective f

/-- Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 6.2 Cores, page 104. -/
def _root_.SimpleGraph.HasCore {V W : Type*} [Fintype V] [Fintype W]
    (X : SimpleGraph V) (Y : SimpleGraph W) : Prop :=
  Y.IsCore ∧ Nonempty (X →g Y) ∧ ∃ f : Y →g X, Function.Injective f

-- Combinatorics 23: Local injection

/-- As usual we add in "finite" since all graphs in Godsil/Royle are assumed to be finite.

Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8, page 115.
-/
def _root_.SimpleGraph.IsLocalInjection {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) : Prop :=
  ∀ a b : V, f a = f b → a ≠ b → 3 ≤ G.edist a b

-- Combinatorics 24: Local isomorphism

/-- Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8 Foldings and Covers, page
115.
-/
def _root_.SimpleGraph.IsLocalIsomorphism {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) : Prop :=
  ∀ x : V, Set.BijOn f (G.neighborSet x) (H.neighborSet (f x))

-- Combinatorics 429: Covers (graph)

/-- Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8 Foldings and Covers, page
115.
-/
def _root_.SimpleGraph.Covers {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : G →g H, G.IsLocalIsomorphism H f ∧ Function.Surjective f

-- Combinatorics 441: Folding

def _root_.SimpleGraph.IsSimpleFolding.{u} {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) : Prop :=
  ∃ a b : V, a ≠ b ∧ G.edist a b = 2 ∧ f a = f b ∧
    ∀ x y : V, f x = f y → x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

/-- Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8 Foldings and Covers, page
114.
-/
inductive _root_.SimpleGraph.IsFolding.{u} : ∀ {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    (_f : G →g H), Prop where
  | id {V : Type u} {G : SimpleGraph V} : IsFolding G G Hom.id
  | simple {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) :
      G.IsSimpleFolding H f → IsFolding G H f
  | comp {V W X : Type u} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}
      (f : G →g I) (g : I →g H) :
      IsFolding G I f → IsFolding I H g → IsFolding G H (g.comp f)

end MetaMathlibExt

end
