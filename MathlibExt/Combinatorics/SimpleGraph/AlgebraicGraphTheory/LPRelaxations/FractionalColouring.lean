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

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 437, Combinatorics 438

/-!
# FractionalColouring

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 437, Combinatorics 438

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 7.1, page 135-136. (for
  `SimpleGraph.fracChromaticNumber`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 7.1 Fractional Colourings and Cliques,
  page 136. (for `FracColouring.IsRegular`)
-/

namespace MetaMathlibExt

-- Combinatorics 437: Fractional colouring & fractional chromatic number

structure FracColouring {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) where
  w : Finset V → ℝ
  nonneg : ∀ s, 0 ≤ w s
  indep : ∀ s, w s ≠ 0 → G.IsIndepSet (s : Set V)
  cover : ∀ v : V, 1 ≤ ∑ s ∈ Finset.univ.filter (fun s => v ∈ s), w s

def FracColouring.weight {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (c : FracColouring G) : ℝ :=
  ∑ s ∈ Finset.univ, c.w s

/-- Note that Godsil/Royle cheat a bit in their definition, defining the fractional chromatic number
to be the MINIMUM instead of the INFIMUM and justify this later. In the natural language statement,
I use infimum, with the idea that later there would be simple theorems justifying that the
fractional chromatic number is actually attainable by some fractional colouring (and that it is
rational).

Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 7.1, page 135-136.
-/
noncomputable def _root_.SimpleGraph.fracChromaticNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  sInf {q : ℝ | ∃ c : FracColouring G, c.weight = q}

-- Combinatorics 438: Regular fractional colouring

/-- Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 7.1 Fractional Colourings and
Cliques, page 136.
-/
def FracColouring.IsRegular {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (c : FracColouring G) : Prop :=
  ∀ u : V,
    (∑ s ∈ Finset.univ.filter (fun s => u ∈ s), c.w s) = 1

end MetaMathlibExt

end
