/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial reflection

This file describes how substituting `-X` changes polynomial coefficients.
-/

namespace Polynomial

/-- Substituting `-X` multiplies the coefficient of degree `n` by `(-1) ^ n`. -/
@[simp]
theorem coeff_comp_neg_X {R : Type*} [CommRing R] (p : R[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1 : R) ^ n * p.coeff n := by
  rw [show (-X : R[X]) = C (-1) * X by simp, comp_C_mul_X_coeff, mul_comm]

end Polynomial
