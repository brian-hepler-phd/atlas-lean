/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.MotzkinCentralTrinomial
import Lean.Elab.Tactic.Omega

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-! # Motzkin numbers

The Motzkin numbers (OEIS A001006) as the Catalan-weighted binomial sum
`M(n) = ∑_{k=0}^{n} C(n,2k) C(k)`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2).
-/

/-- The Motzkin numbers (OEIS A001006) `M(n) = ∑_{k=0}^{n} C(n,2k) C(k)`, with `C(k)` the
Catalan numbers (OEIS A000108). Terms with `2k > n` vanish.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
def motzkinNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose (2 * k) * catalan k

/-- `M(0) = 1`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
theorem motzkinNumber_zero : motzkinNumber 0 = 1 := by
  simp [motzkinNumber]

/-- `M(1) = 1`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
theorem motzkinNumber_one : motzkinNumber 1 = 1 := by
  simp [motzkinNumber, Finset.sum_range_succ]

/-- `M(2) = 2`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
theorem motzkinNumber_two : motzkinNumber 2 = 2 := by
  simp [motzkinNumber, Finset.sum_range_succ, catalan_one,
    Nat.choose_eq_zero_of_lt (by norm_num : 2 < 4)]

/-- The defining sum may stop at `k = ⌊n/2⌋`, since `C(n,2k) = 0` for `2k > n`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
theorem motzkinNumber_eq_sum_range_half (n : ℕ) :
    motzkinNumber n = ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * catalan k := by
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hnot
    simp only [Finset.mem_range] at hk hnot
    rw [Nat.choose_eq_zero_of_lt (by omega : n < 2 * k), Nat.zero_mul]

/-- The central trinomial coefficients satisfy `T(n+1) = T(n) + 2n M(n-1)` for `n ≥ 1`
(`MetaMathlibExt.motzkin_central_trinomial_recurrence` specialized to `motzkinNumber`).

Source: P. Blasiak, G. Dattoli, A. Horzela, K. A. Penson, and K. Zhukovsky, *Motzkin Numbers,
Central Trinomial Coefficients and Hybrid Polynomials*, Journal of Integer Sequences 11 (2008),
Article 08.1.1, equation (34). -/
theorem trinomialCoefficient_succ_eq_add_motzkinNumber (n : ℕ) (hn : 1 ≤ n) :
    trinomialCoefficient (n + 1) (n + 1) =
      trinomialCoefficient n n + 2 * n * motzkinNumber (n - 1) :=
  motzkin_central_trinomial_recurrence motzkinNumber motzkinNumber_eq_sum_range_half n hn

end

end MetaMathlibExt
