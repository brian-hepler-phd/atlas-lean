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

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 1

open SimpleGraph Finset

/-!
# GeneralizedJohnson

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 1

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.6, page 9. (for `johnsonGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 1: Generalized Johnson graph

/-- The definition in the text is for positive integers, but later Kneser graphs are defined with
$i=0$, so I have chosen to include this possibility.

The graphs are never actually called "generalized Johnson graphs" in the book but they are defined
in the section called "Johnson graphs", so I elected to use this name.

Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 1.6, page 9.
-/
def johnsonGraph (v k i : ℕ) :
    SimpleGraph {S : Finset (Fin v) // S.card = k} where
  Adj A B := A ≠ B ∧ (A.val ∩ B.val).card = i
  symm := ⟨fun {A B} ⟨hne, hcard⟩ => ⟨hne.symm, by rw [inter_comm]; exact hcard⟩⟩
  loopless := ⟨fun {A} ⟨hne, _⟩ => hne rfl⟩

end MetaMathlibExt

end
