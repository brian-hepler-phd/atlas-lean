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

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 432

/-!
# EdgeTranspositionGraph

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 432

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 3.10, page 52. (for
  `edgeTranspositionGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 432: Edge-transposition graph

/-- Godsil & Royle do not give a name to this graph. I am calling it the edge-transposition graph,
since the name "transposition graph" already exists (this is the Cayley graph $X(S_n,T)$ where $T$
is the set of all transpositions of $S_n$).

Note also that there is a pythonic-indexing thing going on since Fin n is the set
$\{0,1,\dots,n-1\}$.

Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 3.10, page 52.
-/
def edgeTranspositionGraph {n : ℕ} (T : Set (Equiv.Perm (Fin n))) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => Equiv.swap i j ∈ T)

end MetaMathlibExt

end
