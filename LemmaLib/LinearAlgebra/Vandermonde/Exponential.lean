/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Vandermonde

import Mathlib.Tactic.Ring

/-!
# Exponential Vandermonde matrices

This file proves that finitely many real exponentials with distinct exponents are linearly
independent when sampled at consecutive natural numbers.
-/

public section

namespace Matrix

private theorem exp_neg_injective {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t) :
    Function.Injective (fun i ↦ Real.exp (-t i)) := by
  intro i j hij
  apply ht
  exact neg_injective (Real.exp_injective hij)

/-- The Vandermonde determinant on distinct nodes of the form `exp (-t i)` is nonzero. -/
theorem det_vandermonde_exp_neg_ne_zero {n : ℕ} (t : Fin n → ℝ)
    (ht : Function.Injective t) :
    (vandermonde fun i : Fin n ↦ Real.exp (-t i)).det ≠ 0 := by
  exact det_vandermonde_ne_zero_iff.mpr (exp_neg_injective t ht)

/-- A linear combination of exponentials with distinct real exponents is zero if it vanishes at the
first `n` natural numbers, where `n` is the number of terms. -/
theorem eq_zero_of_sum_mul_exp_neg_eq_zero {n : ℕ} (t c : Fin n → ℝ)
    (ht : Function.Injective t)
    (hzero : ∀ k : Fin n, ∑ i : Fin n, c i * Real.exp (-(k : ℕ) * t i) = 0) :
    c = 0 := by
  apply eq_zero_of_forall_pow_sum_mul_pow_eq_zero (exp_neg_injective t ht)
  intro k
  calc
    ∑ i : Fin n, c i * Real.exp (-t i) ^ (k : ℕ) =
        ∑ i : Fin n, c i * Real.exp ((k : ℝ) * (-t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.exp_nat_mul]
    _ = ∑ i : Fin n, c i * Real.exp (-(k : ℝ) * t i) := by
      congr 1
      funext i
      congr 2
      ring
    _ = 0 := hzero k

end Matrix
