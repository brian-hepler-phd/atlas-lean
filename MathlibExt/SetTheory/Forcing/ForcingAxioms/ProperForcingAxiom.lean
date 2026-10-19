/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Order.PFilter
public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets
public import MathlibExt.SetTheory.Forcing.ForcingAxioms.MartinAxiom
public import MathlibExt.SetTheory.Forcing.ForcingAxioms.Proper

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 49, Logic 562

/-!
# Proper Forcing Axiom; Proper Forcing Axiom theorems (part I)

## References

* Jech (for `ProperForcingAxiom`)
* 1. isPFilter_principal — the principal set ${x : p \le x}$ is a filter. Source: Mathlib,
  Order.PFilter.principal, Mathlib/Order/PFilter.lean:95–96: "The smallest filter containing a
  given element", with mem_principal : x ∈ principal y ↔ y ≤ x. 2.
  not_pfa_conclusion_without_isCoinitial — the PFA conclusion minus the cofinality hypothesis is
  refutable in ZFC, (witness $\mathcal D = {\varnothing}$). Source: direct observation, original
  to this formalization. Background: the, PFA conclusion in J. Baumgartner, "Applications of the
  proper forcing axiom", in Handbook of Set-Theoretic Topology, (Kunen–Vaughan, eds.),
  North-Holland, Amsterdam, 1984, pp. 914–959. 3. exists_pFilter_of_countable — Rasiowa–Sikorski
  (countable dense families admit a generic filter through $p$). Sources: original, H. Rasiowa and
  R. Sikorski, "A proof of the completeness theorem of Gödel", Fundamenta Mathematicae, 37 (1950),
  193–200, doi:10.4064/fm-37-1-193-200; textbook, T. Jech, Set Theory, 3rd ed., Springer, 2003,
  Chapter 14, (Forcing).
-/

open Cardinal Ordinal Set Order

namespace MetaMathlibExt

-- Logic 49: Proper Forcing Axiom

/-- Source: Jech. -/
def ProperForcingAxiom : Prop :=
  ∀ (P : Type*) [PartialOrder P], IsProperForcing P →
    ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ aleph 1 →
    ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

end MetaMathlibExt

end
