/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Linarith

/-!
# Derivatives of even functions

This file proves that an even real function has derivative zero at the origin whenever that
function is differentiable there.
-/

public section

/-- The derivative of an even real function at the origin is zero. -/
theorem HasDerivAt.eq_zero_of_even {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0)
    (heven : Function.Even f) : f' = 0 := by
  have hneg : HasDerivAt (f ∘ Neg.neg) (f' * (-1 : ℝ)) 0 := by
    simpa using HasDerivAt.comp_of_eq (0 : ℝ) hf (hasDerivAt_neg (0 : ℝ)) (by simp)
  have hsame : f ∘ Neg.neg = f := by
    funext x
    exact heven x
  rw [hsame] at hneg
  linarith [hf.unique hneg]

/-- An even real function differentiable at the origin has derivative zero there. -/
theorem Function.Even.deriv_zero {f : ℝ → ℝ} (heven : Function.Even f)
    (hf : DifferentiableAt ℝ f 0) : deriv f 0 = 0 :=
  hf.hasDerivAt.eq_zero_of_even heven
