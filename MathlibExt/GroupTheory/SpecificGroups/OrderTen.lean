/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.SpecificGroups.Dihedral.IndexTwo
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Noncyclic groups of order ten

Adapted from `v1/Atlas/AlgebraNotes/code/SylowTheorems.lean`, lines 108-313 at
commit `8de8f74fa5760eb8b768a9804494ca2ab631cf87`.
The public statement preserves the archived code's domains and hypotheses.
This provenance is code-to-code, not verification of the unavailable textbook PDF.
-/
set_option autoImplicit false

namespace MetaMathlibExt
@[expose] public section
open Finset Nat MulAction Subgroup

private lemma conjugation_pow_four
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) (hnc : ¬IsCyclic G)
    (x y : G) (hx5 : orderOf x = 5) (hy2 : orderOf y = 2) :
    y * x * y⁻¹ = x ^ 4 := by
  classical
  have hy_sq : y * y = 1 := by
    simpa [sq] using (show y ^ 2 = 1 from by rw [← hy2]; exact pow_orderOf_eq_one y)
  have hy_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy_sq
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx5, Nat.card_eq_fintype_card, hG] at h
    omega
  have hN : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hindex
  have hconj_mem : y * x * y⁻¹ ∈ Subgroup.zpowers x :=
    hN.conj_mem x (Subgroup.mem_zpowers x) y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj_mem

  have hkk : x ^ (k * k) = x := by
    have hphi : y * x ^ k * y⁻¹ = (y * x * y⁻¹) ^ k := conj_zpow.symm
    rw [hk.symm, ← zpow_mul] at hphi

    have hphi2 : y * (y * x * y⁻¹) * y⁻¹ = x := by
      rw [hy_inv]
      calc y * (y * x * y) * y = (y * y) * x * (y * y) := by group
        _ = x := by rw [hy_sq, one_mul, mul_one]

    rw [hk] at hphi

    rw [hphi2] at hphi

    exact hphi.symm

  have h5dvd : (5 : ℤ) ∣ k * k - 1 := by
    have h1 : x ^ (k * k - 1) = 1 := by
      have : x ^ (k * k) * x⁻¹ = 1 := by rw [hkk, mul_inv_cancel]
      rwa [← zpow_neg_one, ← zpow_add] at this
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hx5] at h2; exact_mod_cast h2
  have hk_mod : k % 5 = 1 ∨ k % 5 = 4 := by
    have hmod5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    have hkey : (k % 5) * (k % 5) % 5 = 1 := by
      have h3 : (k * k) % 5 = 1 := by omega
      have h4 : (k * k) % 5 = (k % 5 * (k % 5)) % 5 := Int.mul_emod k k 5
      omega
    rcases hmod5 with h | h | h | h | h <;> simp_all
  rcases hk_mod with hk1 | hk4
  ·
    exfalso; apply hnc
    have hyx_eq_x : y * x * y⁻¹ = x := by
      rw [← hk]; conv_lhs => rw [← zpow_mod_orderOf x k]
      rw [hx5]; simp only [Nat.cast_ofNat]
      rw [show k % (5 : ℤ) = 1 from hk1]; simp
    have hcomm : Commute x y := by
      have h : x * y = y * x := by
        have h1 : y * x * y⁻¹ = x := hyx_eq_x
        have h2 : y * x = x * y := by
          calc y * x = y * x * y⁻¹ * y := by rw [inv_mul_cancel_right]
            _ = x * y := by rw [h1]
        exact h2.symm
      exact h
    have hord : orderOf (x * y) = 10 := by
      have := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx5, hy2]; norm_num)
      rw [hx5, hy2] at this; exact this
    exact isCyclic_of_orderOf_eq_card (x * y) (by rw [hord, Nat.card_eq_fintype_card, hG])
  ·
    rw [← hk]; conv_lhs => rw [← zpow_mod_orderOf x k]
    rw [hx5]; simp only [Nat.cast_ofNat]
    rw [show k % (5 : ℤ) = 4 from hk4]
    norm_num

private lemma outside_square_one
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) (hnc : ¬IsCyclic G)
    (x y : G) (hx5 : orderOf x = 5) (hy2 : orderOf y = 2) :
    ∀ g : G, g ∉ Subgroup.zpowers x → g ^ 2 = 1 := by
  classical
  have hy_sq : y * y = 1 := by
    simpa [sq] using (show y ^ 2 = 1 from by rw [← hy2]; exact pow_orderOf_eq_one y)
  have hy_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy_sq
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx5, Nat.card_eq_fintype_card, hG] at h
    omega
  have hy_not : y ∉ Subgroup.zpowers x := by
    intro hy
    have h := Subgroup.orderOf_dvd_natCard _ hy
    rw [Nat.card_zpowers, hx5, hy2] at h
    omega
  have hx5one : x ^ 5 = 1 := by
    rw [← hx5]
    exact pow_orderOf_eq_one x
  have hfour : x ^ 4 = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc x ^ 4 * x = x ^ 5 := (pow_succ x 4).symm
         _ = 1 := hx5one
  have hconj_inverse : y * x * y⁻¹ = x⁻¹ :=
    (conjugation_pow_four G hG hnc x y hx5 hy2).trans hfour
  intro g hg
  have hmul : y⁻¹ * g ∈ Subgroup.zpowers x := by
    rw [Subgroup.mul_mem_iff_of_index_two hindex]
    simp [hy_not, hg]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmul
  have hdecomp : g = y * x ^ k := by
    rw [hk]
    group
  have hconjk : y * x ^ k * y⁻¹ = (x ^ k)⁻¹ := by
    calc y * x ^ k * y⁻¹ = (y * x * y⁻¹) ^ k := conj_zpow.symm
         _ = (x⁻¹) ^ k := by rw [hconj_inverse]
         _ = (x ^ k)⁻¹ := by simp
  rw [hdecomp, sq]
  calc (y * x ^ k) * (y * x ^ k) = (y * x ^ k * y⁻¹) * x ^ k := by
         rw [hy_inv]
         group
       _ = (x ^ k)⁻¹ * x ^ k := by rw [hconjk]
       _ = 1 := inv_mul_cancel _

/-- Every noncyclic group of cardinality ten is isomorphic to the dihedral group of
order ten. The generators and inversion argument are adapted from the archived
AlgebraNotes source; the final isomorphism uses the shared index-two constructor. -/
theorem nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) (hnc : ¬IsCyclic G) :
    Nonempty (G ≃* DihedralGroup 5) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card 5 (by omega : (5 : ℕ) ∣ Fintype.card G)
  obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card 2 (by omega : (2 : ℕ) ∣ Fintype.card G)
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx5, Nat.card_eq_fintype_card, hG] at h
    omega
  have houtside : ∀ g : G, g ∉ Subgroup.zpowers x → g ^ 2 = 1 :=
    outside_square_one G hG hnc x y hx5 hy2
  have h := nonempty_mulEquiv_dihedralGroup_of_index_eq_two
    (Subgroup.zpowers x) (inferInstance : IsCyclic (Subgroup.zpowers x)) hindex houtside
  have hcard : Nat.card (Subgroup.zpowers x) = 5 := by
    rw [Nat.card_zpowers, hx5]
  rw [hcard] at h
  exact h

end

end MetaMathlibExt
