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
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 18

/-!
# CoxeterGraph

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 18

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 4.6 The Coxeter Graph, page 69. (for
  `coxeterGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 18: Coxeter graph

def fin4ToZMod7 : Fin 4 → ZMod 7
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- Note that the textbook definition appearing in the verbatim statement has some ambiguity that we
fix in the natural language statement. Their ambiguity arises because they have an accompanying
figure, and also an alternate explicit description of the Coxeter graph as an induced subgraph of
the Kneser graph $J(7,3,0)$.

Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 4.6 The Coxeter Graph, page 69.
-/
def coxeterGraph : SimpleGraph (Fin 4 × ZMod 7) :=
  SimpleGraph.fromRel fun a b =>
    (a.1 = b.1 ∧ a.1 ≠ 0 ∧ a.2 - b.2 = fin4ToZMod7 a.1)
    ∨
    (a.1 = 0 ∧ b.1 ≠ 0 ∧ a.2 = b.2)

end MetaMathlibExt

end
