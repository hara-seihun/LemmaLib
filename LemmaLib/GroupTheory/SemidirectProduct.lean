/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Subgroups of semidirect products

This file records normality properties of the distinguished factors of a semidirect product.
-/

namespace SemidirectProduct

/-- The intersection of a subgroup of a semidirect product with the left factor is normal in that
subgroup. -/
theorem normal_subgroupOf_range_inl {N H : Type*} [Group N] [Group H] (φ : H →* MulAut N)
    (K : Subgroup (N ⋊[φ] H)) :
    ((inl : N →* N ⋊[φ] H).range.subgroupOf K).Normal := by
  rw [range_inl_eq_ker_rightHom]
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact Subgroup.le_normalizer_of_normal

end SemidirectProduct
