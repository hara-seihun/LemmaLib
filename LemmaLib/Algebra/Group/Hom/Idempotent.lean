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

namespace AddMonoidHom

/-- An additive homomorphism to a left-cancellative additive monoid sends every additive
idempotent to zero. -/
theorem map_eq_zero_of_add_eq_self {M N : Type*} [AddMonoid M] [AddLeftCancelMonoid N]
    (f : M →+ N) {x : M} (hx : x + x = x) : f x = 0 := by
  apply add_left_cancel (a := f x)
  simpa only [map_add, add_zero] using congrArg f hx

/-- A biadditive map into a left-cancellative additive monoid vanishes when its first argument is an
additive idempotent. -/
theorem map_apply_eq_zero_of_add_eq_self {M N P : Type*} [AddMonoid M] [AddMonoid N]
    [AddCancelCommMonoid P] (B : M →+ N →+ P) {x : M} (hx : x + x = x) (y : N) :
    B x y = 0 := by
  apply add_eq_right.mp
  calc
    B x y + B x y = B (x + x) y := by rw [map_add, AddMonoidHom.add_apply]
    _ = B x y := by rw [hx]

/-- A biadditive map into a left-cancellative additive monoid vanishes when its second argument is
an additive idempotent. -/
theorem apply_map_eq_zero_of_add_eq_self {M N P : Type*} [AddMonoid M] [AddMonoid N]
    [AddCancelCommMonoid P] (B : M →+ N →+ P) (x : M) {y : N} (hy : y + y = y) :
    B x y = 0 :=
  (B x).map_eq_zero_of_add_eq_self hy

end AddMonoidHom
