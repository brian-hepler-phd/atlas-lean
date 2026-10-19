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
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 26

/-!
# Andrasfai

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 26

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.10 The Andrásfai Graphs, page 118. (for
  `andrasfaiGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 26: Andrásfai graph

def andrasfaiConnectionSet (k : ℕ) : Finset (ZMod (3 * k + 2)) :=
  {x | x.val % 3 = 1}

/-- I have made the definition using $3k+2$ instead of $3k-1$. The point of this is that one can now
just take $k : \N$ instead of enforcing $k \ge 1$, and also there are no issues in proofs where we
have to explicitly state that things will be positive (these annoyances always seem to happen with
subtraction of nats).

Source: Algebraic Graph Theory, Godsil & Royle (2001), Section 6.10 The Andrásfai Graphs, page 118.
-/
def andrasfaiGraph (k : ℕ) : SimpleGraph (ZMod (3 * k + 2)) :=
  SimpleGraph.addCayley (andrasfaiConnectionSet k)

end MetaMathlibExt

end
