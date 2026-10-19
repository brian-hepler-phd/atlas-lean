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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.GeneralizedJohnson

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 439

/-!
# Kneser

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 439

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.6 Johnson graphs, page 9. (for
  `kneserGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 439: Kneser graph

/-- The Godsil-Royle text defines Kneser graphs twice, and DIFFERENTLY! The first time they insist
that $v \ge 2k$ (I have removed this to avoid confusion), since for all values of $k$ with $2k \ge
v$ we get the same graph of $v$ disconnected vertices (by size considerations each pair of sets
cannot be disjoint so no pair of vertices is adjacent). However, this causes problems later when
they state that the fractional chromatic number of a finite graph $X$ is the minimum ratio $v/k$
such that there is a homomorphism from $X$ to the Kneser graph $K_{v:k}$. In this section they
actually use the following definition:

The Kneser graph $K_{v:r}$ is the graph with the $r$-subsets of a fixed $v$-set as its vertices with
two $r$-subsets adjacent if they are disjoint. (Chapter 7 Kneser graphs, page 135).

Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 1.6 Johnson graphs, page 9.
-/
def kneserGraph (v k : ℕ) :
    SimpleGraph {S : Finset (Fin v) // S.card = k} :=
  johnsonGraph v k 0

end MetaMathlibExt

end
