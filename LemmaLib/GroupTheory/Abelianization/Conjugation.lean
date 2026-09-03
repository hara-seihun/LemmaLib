/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Conjugation in the abelianization

Inner conjugation acts trivially after passage to the abelianization.
-/

public section

namespace Abelianization

/-- Conjugate elements have the same image in the abelianization. -/
@[simp]
theorem of_mul_mul_inv {G : Type*} [Group G] (a x : G) :
    of (a * x * a⁻¹) = of x := by
  simp [map_mul, mul_assoc]

end Abelianization
