/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SpecificGroups.OrderTen

/-! Consumers of the shared dihedral constructor and the order-ten classification. -/
set_option autoImplicit false

namespace MetaMathlibExt

-- The order-two example: the cyclic subgroup has order two; the ambient group is D₂.
example : Nonempty (DihedralGroup 2 ≃* DihedralGroup 2) := by
  classical
  let H : Subgroup (DihedralGroup 2) := Subgroup.zpowers (DihedralGroup.r (1 : ZMod 2))
  have hHcard : Nat.card H = 2 := by
    change Nat.card (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 2))) = 2
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hindex : H.index = 2 := by
    have h := H.card_mul_index
    rw [hHcard, DihedralGroup.nat_card] at h
    omega
  have houtside : ∀ g : DihedralGroup 2, g ∉ H → g ^ 2 = 1 := by
    intro g _
    cases g with
    | r i =>
        rw [DihedralGroup.r_pow]
        have hcast : (Nat.cast (2 : ℕ) : ZMod 2) = 0 := by decide
        rw [hcast, mul_zero, DihedralGroup.r_zero]
    | sr i => rw [sq, DihedralGroup.sr_mul_self]
  have h := nonempty_mulEquiv_dihedralGroup_of_index_eq_two H
    (inferInstance : IsCyclic H) hindex houtside
  rw [hHcard] at h
  exact h

-- Use the generic constructor at the actual order-ten dihedral group.
example : Nonempty (DihedralGroup 5 ≃* DihedralGroup 5) := by
  classical
  let H : Subgroup (DihedralGroup 5) := Subgroup.zpowers (DihedralGroup.r (1 : ZMod 5))
  have hHcard : Nat.card H = 5 := by
    change Nat.card (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 5))) = 5
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hindex : H.index = 2 := by
    have h := H.card_mul_index
    rw [hHcard, DihedralGroup.nat_card] at h
    omega
  have houtside : ∀ g : DihedralGroup 5, g ∉ H → g ^ 2 = 1 := by
    intro g hg
    cases g with
    | r i =>
        exfalso
        apply hg
        change DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod 5))
        have h := Subgroup.pow_mem (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 5)))
          (Subgroup.mem_zpowers (DihedralGroup.r (1 : ZMod 5))) i.val
        simpa [DihedralGroup.r_pow] using h
    | sr i => rw [sq, DihedralGroup.sr_mul_self]
  have h := nonempty_mulEquiv_dihedralGroup_of_index_eq_two H
    (inferInstance : IsCyclic H) hindex houtside
  rw [hHcard] at h
  exact h

-- The noncyclic order-ten theorem has a concrete admissible instance.
example : Nonempty (DihedralGroup 5 ≃* DihedralGroup 5) :=
  nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic (DihedralGroup 5)
    (by simpa using (DihedralGroup.card (n := 5)))
    (DihedralGroup.not_isCyclic (by decide : (5 : ℕ) ≠ 1))

-- A separate caller checks the public module boundary and exact source-shaped binders.
example (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) (hnc : ¬IsCyclic G) :
    Nonempty (G ≃* DihedralGroup 5) :=
  nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic G hG hnc

-- The generic constructor also covers the boundary case of a trivial
-- rotation subgroup: `DihedralGroup 1` from `⊥` (and D₁ is cyclic).
example : Nonempty (DihedralGroup 1 ≃* DihedralGroup 1) := by
  have h := nonempty_mulEquiv_dihedralGroup_of_index_eq_two
    (⊥ : Subgroup (DihedralGroup 1)) inferInstance
    (by rw [Subgroup.index_bot, DihedralGroup.nat_card]) (by
      intro g _
      cases g with
      | r i =>
        fin_cases i
        decide
      | sr i =>
        fin_cases i
        decide)
  rwa [Nat.card_unique] at h

example : IsCyclic (DihedralGroup 1) := DihedralGroup.isCyclic_iff.mpr rfl

#print axioms nonempty_mulEquiv_dihedralGroup_of_index_eq_two
#print axioms nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic

end MetaMathlibExt
