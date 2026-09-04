/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The heat-deformed Riemann ξ function

For real `t` and complex `z`, de Bruijn's deformation of the Riemann ξ function is

`H t z = ∫ u in Ioi 0, exp (t * u ^ 2) * Φ u * cos (z * u)`,

where `Φ` is Riemann's kernel

`Φ u = ∑ n ≥ 1, (2 π² n⁴ e^{9u} - 3 π n² e^{5u}) e^{-π n² e^{4u}}`.

`H 0 z = ξ ((1 + i z) / 2) / 8`, so the Riemann hypothesis is the statement that `H 0` has only
real zeros, and the de Bruijn–Newman constant `Λ` is the infimum of the `t` for which `H t` has only
real zeros.

These definitions are the ones registered against the de Bruijn–Newman problem in lemma dev; they
are repeated here verbatim so that later results can be stated about the same object.
-/

public section

open Real

namespace DeBruijnNewman

/-- Riemann's kernel `Φ u = ∑ n ≥ 1, (2 π² n⁴ e^{9u} - 3 π n² e^{5u}) e^{-π n² e^{4u}}`. -/
noncomputable def phi (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    let m : ℝ := ((n + 1 : ℕ) : ℝ)
    (2 * Real.pi ^ 2 * m ^ 4 * Real.exp (9 * u) -
      3 * Real.pi * m ^ 2 * Real.exp (5 * u)) *
      Real.exp (-(Real.pi * m ^ 2 * Real.exp (4 * u)))

/-- The heat-deformed ξ function `H t z = ∫ u in Ioi 0, exp (t u²) Φ u cos (z u)`. -/
noncomputable def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ioi 0,
    (Real.exp (t * u ^ 2) * phi u : ℝ) * Complex.cos (z * u)

/-- `H t` has only real zeros. -/
def OnlyRealZeros (t : ℝ) : Prop :=
  ∀ z : ℂ, H t z = 0 → z.im = 0

/-- `U` is an upper bound for the de Bruijn–Newman constant. -/
def IsUpperBound (U : ℝ) : Prop :=
  ∀ t : ℝ, U ≤ t → OnlyRealZeros t

end DeBruijnNewman
