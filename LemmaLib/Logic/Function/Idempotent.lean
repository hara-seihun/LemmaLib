/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Dynamics.FixedPoints.Defs

/-!
# Idempotent functions

This file relates the range and fixed points of an idempotent function.
-/

public section

open Set

namespace Function

/-- The range of an idempotent function is its set of fixed points. -/
theorem range_eq_fixedPoints_of_idempotent {α : Type*} {f : α → α}
    (hf : ∀ x, f (f x) = f x) : range f = fixedPoints f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact hf y
  · intro hx
    exact ⟨x, mem_fixedPoints_iff.mp hx⟩

end Function
