/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Two-dimensional matrix identities

This file records identities special to two-by-two matrices.
-/

namespace Matrix

/-- Every two-by-two matrix preserves the standard alternating form up to multiplication by its
determinant. -/
theorem transpose_mul_finTwo_alternating_mul {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) :
    A.transpose * !![0, 1; -1, 0] * A =
      A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

end Matrix
