/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Data.Matrix.Mul

/-!
# Skew-symmetric matrices

This file records properties of quadratic forms associated with skew-symmetric matrices.
-/

public section

namespace Matrix

/-- The quadratic form associated with a skew-symmetric matrix over a ring of characteristic zero
vanishes identically. -/
theorem dotProduct_mulVec_eq_zero_of_transpose_eq_neg {n R : Type*} [Fintype n] [CommRing R]
    [NoZeroDivisors R] [CharZero R] (A : Matrix n n R) (hA : A.transpose = -A) (x : n → R) :
    dotProduct x (A.mulVec x) = 0 := by
  let q := dotProduct x (A.mulVec x)
  have htranspose : dotProduct x (A.transpose.mulVec x) = q := by
    calc
      dotProduct x (A.transpose.mulVec x) = dotProduct x (vecMul x A) := by
        rw [mulVec_transpose]
      _ = dotProduct (vecMul x A) x := dotProduct_comm _ _
      _ = q := (dotProduct_mulVec x A x).symm
  have hq : q = -q := by
    calc
      q = dotProduct x (A.transpose.mulVec x) := htranspose.symm
      _ = dotProduct x ((-A).mulVec x) := by rw [hA]
      _ = -q := by
        simp only [neg_mulVec, dotProduct_neg]
        rfl
  exact CharZero.eq_neg_self_iff.mp hq

end Matrix
