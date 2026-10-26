/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Additive homomorphisms and idempotent elements

This file shows that additive homomorphisms into a cancellative monoid annihilate additive
idempotents.
-/

public section

namespace AddMonoidHom

/-- An additive homomorphism to a left-cancellative additive monoid sends every additive
idempotent to zero. -/
theorem map_eq_zero_of_add_eq_self {M N : Type*} [AddMonoid M] [AddLeftCancelMonoid N]
    (f : M →+ N) {x : M} (hx : x + x = x) : f x = 0 := by
  apply add_left_cancel (a := f x)
  simpa only [map_add, add_zero] using congrArg f hx

end AddMonoidHom
