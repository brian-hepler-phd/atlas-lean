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

public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.List.GetD
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.IntervalCases

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 490, Combinatorics 494, Combinatorics 495, Combinatorics 497, Combinatorics 498, Combinatorics 500

/-!
# `MathlibExt.Combinatorics.SymmetricFunctionsYoungTableaux`

## References

* ec2 7.8.2 (for `MvPolynomial.omegaAlgHom`)
* ec2 7.8 p 304 (for `MvPowerSeries.exponentialSpecialization`)
* ec2 7.15 p 336 (for `symmetricScalarProduct`)
* ec2 7.10 p 309 (for `SkewShape`, `SkewSemistandardYoungTableau`)
* ec2 7.10 p 312 (for `SkewStandardYoungTableau`)
-/

namespace MetaMathlibExt

-- Combinatorics 490: Omega Involution


/-- The map $\omega$ depends on the number of variables. This number
is not given separately. It is $n$, the number of elements of
$V$, and it is fixed once $V$ is fixed.

Source: ec2 7.8.2.
-/
noncomputable def MvPolynomial.omegaAlgHom (σ R : Type*)
    [CommRing R] [Fintype σ] [DecidableEq σ] :
    MvPolynomial.symmetricSubalgebra σ R →ₐ[R]
      MvPolynomial.symmetricSubalgebra σ R :=
  (MvPolynomial.aeval fun i : Fin (Fintype.card σ) =>
      (⟨MvPolynomial.hsymm σ R (i + 1),
        (MvPolynomial.mem_symmetricSubalgebra _).2
          (MvPolynomial.hsymm_isSymmetric σ R _)⟩ :
        MvPolynomial.symmetricSubalgebra σ R)).comp
    (MvPolynomial.esymmAlgEquiv σ R rfl).symm.toAlgHom

-- Combinatorics 494: Exponential Specialization


/-- The variable $x_i$ is the variable indexed by $i-1$, so
$[x_1\cdots x_m]f$ is the coefficient of the monomial with
exponent $1$ at each of the indices $0,1,\ldots,m-1$ and exponent
$0$ elsewhere.

Source: ec2 7.8 p 304.
-/
noncomputable def _root_.MvPowerSeries.exponentialSpecialization
    (f : MvPowerSeries ℕ ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => (Nat.factorial m : ℚ)⁻¹ *
    MvPowerSeries.coeff
      (∑ i ∈ Finset.range m, Finsupp.single i 1) f

-- Combinatorics 495: Scalar Product of Symmetric Polynomials


/-- Source: ec2 7.15 p 336. -/
noncomputable def symmetricScalarProduct {n : ℕ} {R : Type*}
    [CommRing R]
    (f g : MvPolynomial.symmetricSubalgebra (Fin n) R) : R :=
  let a : MvPolynomial (Fin n) R :=
    ∏ i, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X i - MvPolynomial.X j)
  ∑ β ∈ (a * (f : MvPolynomial (Fin n) R)).support.filter
      (fun β => ∀ i j : Fin n, i < j → β j < β i),
    (a * f).coeff β * (a * g).coeff β

-- Combinatorics 497: Skew Shape


/-- The cell $(i,j)$ is the cell with row index $i-1$ and column
index $j-1$.

Source: ec2 7.10 p 309.
-/
structure SkewShape where
  outer : YoungDiagram
  inner : YoungDiagram
  inner_le_outer : inner ≤ outer

-- Combinatorics 498: Semistandard Young Tableau of Skew Shape


/-- The value $T_{i,j}$ is the entry at row index $i-1$ and column
index $j-1$.

Source: ec2 7.10 p 309.
-/
structure SkewSemistandardYoungTableau (s : SkewShape) where
  entry : ℕ → ℕ → ℕ
  pos : ∀ {i j : ℕ}, (i, j) ∈ s.outer → (i, j) ∉ s.inner →
    0 < entry i j
  row_weak : ∀ {i j1 j2 : ℕ}, j1 < j2 →
    (i, j1) ∈ s.outer → (i, j1) ∉ s.inner →
    (i, j2) ∈ s.outer → (i, j2) ∉ s.inner →
    entry i j1 ≤ entry i j2
  col_strict : ∀ {i1 i2 j : ℕ}, i1 < i2 →
    (i1, j) ∈ s.outer → (i1, j) ∉ s.inner →
    (i2, j) ∈ s.outer → (i2, j) ∉ s.inner →
    entry i1 j < entry i2 j
  zeros : ∀ {i j : ℕ}, ¬ ((i, j) ∈ s.outer ∧ (i, j) ∉ s.inner) →
    entry i j = 0

-- Combinatorics 500: Standard Young Tableau of Skew Shape


/-- The value $T_{i,j}$ is the entry at row index $i-1$ and column
index $j-1$.

Source: ec2 7.10 p 312.
-/
structure SkewStandardYoungTableau (s : SkewShape) extends
    SkewSemistandardYoungTableau s where
  bijOn : Set.BijOn (fun c : ℕ × ℕ => entry c.1 c.2)
    ↑(s.outer.cells \ s.inner.cells)
    (Set.Icc 1 (s.outer.cells \ s.inner.cells).card)

end MetaMathlibExt

end
