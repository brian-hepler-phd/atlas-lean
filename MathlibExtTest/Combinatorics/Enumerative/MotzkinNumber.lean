/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
public import MathlibExt.Combinatorics.Enumerative.AignerMotzkinInequality

namespace MetaMathlibExt

example : motzkinNumber 0 = 1 := motzkinNumber_zero

example : motzkinNumber 2 = 2 := motzkinNumber_two

example : motzkinNumber 3 = 4 := by
  simp [motzkinNumber, Finset.sum_range_succ, Nat.choose, catalan_one, catalan_two, catalan_three]

example : motzkinNumber 4 = 9 := by
  simp [motzkinNumber, Finset.sum_range_succ, Nat.choose, catalan_one, catalan_two, catalan_three]

example : motzkinNumber 5 = 21 := by
  simp [motzkinNumber, Finset.sum_range_succ, Nat.choose, catalan_one, catalan_two, catalan_three]

example : motzkinNumber 6 = 51 := by
  simp [motzkinNumber, Finset.sum_range_succ, Nat.choose, catalan_one, catalan_two, catalan_three]

example : motzkinNumber 7 = 127 := by
  simp [motzkinNumber, Finset.sum_range_succ, Nat.choose, catalan_one, catalan_two, catalan_three]

example : motzkinNumber 7 = ∑ k ∈ Finset.range 4, Nat.choose 7 (2 * k) * catalan k :=
  motzkinNumber_eq_sum_range_half 7

example : ((motzkinNumber 3 : ℚ) - motzkinNumber 2) / ((motzkinNumber 4 : ℚ) - motzkinNumber 3) ≤
    (motzkinNumber 3 : ℚ) / motzkinNumber 4 :=
  motzkinNumber_ratio_inequality 3 (by norm_num)

end MetaMathlibExt
