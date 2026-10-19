/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.List.Cycle
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.FinCases

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 29, Combinatorics 30, Combinatorics 54, Combinatorics 55, Combinatorics 56, Combinatorics 462, Combinatorics 463, Combinatorics 465, Combinatorics 464

/-!
# `MathlibExt.Combinatorics.Fundamentals.SpecialSequences`

## References

* ec1 p 28 (for `LatticePath`)
* ec1 1.105b p 136 (for `Necklace`)
* ec1 1.6 p 115 (for `Nat.lucas`)
* ec1 1.147 p 146 (for `Nat.motzkin`)
* ec1 1.9 p 116 (for `Nat.delannoy`)
* ec1 2.7.1 (for `SoutheastPath`, `SoutheastPath.weight`, `IsNonintersectingPathFamily`,
  `nonintersectingPathWeightSum`)
-/

namespace MetaMathlibExt

-- Combinatorics 29: Lattice Path with Prescribed Steps

/-- Source: ec1 p 28. -/
def LatticePath (d : ℕ)
    (D : Set (Fin d → ℤ))
    (p q : Fin d → ℤ) :=
  { l : List (Fin d → ℤ) //
    l.head? = some p ∧
    l.getLast? = some q ∧
    List.IsChain
      (fun a b => b - a ∈ D) l
  }

-- Combinatorics 30: Fixed-Length Necklace

/-- Usage:

```lean
def redBlueNecklace : Necklace String 2 :=
  ⟨Quotient.mk
      (List.IsRotated.setoid String)
      ["red", "blue"],
    by simp⟩
```

Source: ec1 1.105b p 136.
-/
def Necklace (A : Type*) (n : ℕ) :=
  {c : Cycle A // c.length = n}

-- Combinatorics 54: Lucas Number Sequence

/-- Source: ec1 1.6 p 115. -/
def Nat.lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => Nat.lucas (n + 1) + Nat.lucas n

-- Combinatorics 55: Motzkin Number Sequence

/-- Source: ec1 1.147 p 146. -/
def Nat.motzkin : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    Nat.motzkin n +
      Finset.sum Finset.univ fun k : Fin n =>
        Nat.motzkin k.val *
          Nat.motzkin (n - 1 - k.val)

-- Combinatorics 56: Delannoy Numbers

/-- Source: ec1 1.9 p 116. -/
def Nat.delannoy : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _, 0 => 1
  | m + 1, n + 1 =>
    Nat.delannoy m (n + 1) +
      Nat.delannoy (m + 1) n +
        Nat.delannoy m n

-- Combinatorics 462: Southeast Path


/-- The south step is written as the earlier
point being one higher, matching the source,
rather than as the later point being one
lower. The second form would use truncated
subtraction on $\mathbb Z_{\geq 0}$ and would
wrongly admit a step from a point at height
$0$ to itself.

Source: ec1 2.7.1.
-/
def SoutheastPath (p q : ℕ × ℕ) :=
  { l : List (ℕ × ℕ) //
    l.head? = some p ∧ l.getLast? = some q ∧
    l.IsChain fun a b =>
      b = (a.1 + 1, a.2) ∨ a = (b.1, b.2 + 1) }

-- Combinatorics 463: Southeast Path Weight


/-- Source: ec1 2.7.1. -/
def SoutheastPath.weight {p q : ℕ × ℕ} {R : Type*}
    [CommMonoid R] (x : ℕ → R)
    (l : SoutheastPath p q) : R :=
  ((l.1.zip l.1.tail).map fun c =>
    if c.2 = (c.1.1 + 1, c.1.2) then x c.1.2 else 1).prod

-- Combinatorics 465: Nonintersecting Path Family


/-- Deciding a concrete instance needs both this
definition and the pairwise predicate
unfolded, not just the first.

Source: ec1 2.7.1.
-/
def IsNonintersectingPathFamily {n : ℕ}
    {p q : Fin n → ℕ × ℕ}
    (L : (i : Fin n) → SoutheastPath (p i) (q i)) :
    Prop :=
  Pairwise fun i j => ∀ v ∈ (L i).1, v ∉ (L j).1

-- Combinatorics 464: Nonintersecting Path Weight Sum


/-- The sum ranges over all nonintersecting
families at once, and no finite set of
families comes with it. Rewriting it as a
sum over a finite set needs a proof that
only finitely many southeast paths join two
fixed points.

Source: ec1 2.7.1.
-/
noncomputable def nonintersectingPathWeightSum {n : ℕ}
    {R : Type*} [CommSemiring R] (x : ℕ → R)
    (p q : Fin n → ℕ × ℕ) : R :=
  ∑ᶠ L : {L : (i : Fin n) → SoutheastPath (p i) (q i) //
      IsNonintersectingPathFamily L},
    ∏ i, (L.1 i).weight x

end MetaMathlibExt

end
