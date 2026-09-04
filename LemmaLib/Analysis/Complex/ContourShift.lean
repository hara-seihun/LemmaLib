/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Shifting a contour with Gaussian decay

If `F : ℂ → ℂ` is holomorphic on the closed horizontal strip between `Im v = 0` and `Im v = β`
and satisfies `‖F v‖ ≤ C exp (-a (Re v)²)` there for some `a > 0`, then

`∫ x : ℝ, F (x + β i) = ∫ x : ℝ, F x`

(`Complex.integral_add_ofReal_mul_I_eq_integral`), and consequently `∫ F (x + c) = ∫ F x` for any
complex `c` whose imaginary part is `β` (`Complex.integral_add_eq_integral`). The proof integrates
`F` around the rectangle with vertices `±T`, `±T + β i`, where the vertical sides contribute
`O(exp (-a T²))`, and lets `T → ∞`.

This is the contour shift used to compute the Gaussian heat flow of `s ↦ r₀ n s` in the
de Bruijn–Newman effective model (`LemmaLib.NumberTheory.DeBruijnNewman.RtnEstimate`).
-/

public section

open Complex Real Set Filter Topology MeasureTheory intervalIntegral

namespace Complex

/-- Shifting the contour of an integral over `ℝ` to the horizontal line `Im = β`, for a function
holomorphic on the closed strip between the two lines with Gaussian decay there. -/
theorem integral_add_ofReal_mul_I_eq_integral {F : ℂ → ℂ} {β a C : ℝ} (ha : 0 < a)
    (hF : ∀ v : ℂ, v.im ∈ uIcc 0 β → DifferentiableAt ℂ F v)
    (hbound : ∀ v : ℂ, v.im ∈ uIcc 0 β → ‖F v‖ ≤ C * Real.exp (-a * v.re ^ 2)) :
    ∫ x : ℝ, F (x + β * I) = ∫ x : ℝ, F x := by
  -- continuity and integrability along horizontal lines of the strip
  have hcont : ∀ y ∈ uIcc 0 β, Continuous fun x : ℝ => F (x + y * I) := by
    intro y hy
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h1 : ContinuousAt F (x + y * I) := (hF _ (by simpa using hy)).continuousAt
    exact h1.comp (f := fun x : ℝ => (x : ℂ) + y * I) (by fun_prop)
  have hint : ∀ y ∈ uIcc 0 β, Integrable fun x : ℝ => F (x + y * I) := by
    intro y hy
    refine Integrable.mono' ((integrable_exp_neg_mul_sq ha).const_mul C)
      (hcont y hy).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    simpa using hbound (x + y * I) (by simpa using hy)
  have h0 : (0 : ℝ) ∈ uIcc 0 β := left_mem_uIcc
  have hβ : β ∈ uIcc 0 β := right_mem_uIcc
  -- the rectangle identity
  set V : ℝ → ℂ := fun T => I * ((∫ y in (0 : ℝ)..β, F (T + y * I)) -
    ∫ y in (0 : ℝ)..β, F (-T + y * I)) with hV
  have hC : ∀ T : ℝ, ∫ x in -T..T, F (x + β * I) = (∫ x in -T..T, F x) + V T := by
    intro T
    have := integral_boundary_rect_eq_zero_of_differentiableOn F (-T) (T + β * I) (by
      intro v hv
      refine (hF v ?_).differentiableWithinAt
      rw [mem_reProdIm] at hv
      simpa using hv.2)
    simp only [neg_re, ofReal_re, add_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, neg_im, neg_zero, add_im, mul_im, zero_add, ofReal_zero, zero_mul,
      smul_eq_mul] at this
    rw [hV]
    simp only [ofReal_neg] at this
    linear_combination -this
  -- the vertical integrals vanish in the limit
  have hVle : ∀ T : ℝ, ‖V T‖ ≤ 2 * |β| * (C * Real.exp (-a * T ^ 2)) := by
    intro T
    rw [hV]
    simp only [norm_mul, norm_I, one_mul]
    have key : ∀ T' : ℝ, T' ^ 2 = T ^ 2 →
        ‖∫ y in (0 : ℝ)..β, F (T' + y * I)‖ ≤ C * Real.exp (-a * T ^ 2) * |β - 0| := by
      intro T' hT'
      refine norm_integral_le_of_norm_le_const fun y hy => ?_
      have := hbound (T' + y * I) (by simpa using uIoc_subset_uIcc hy)
      simpa [hT'] using this
    calc ‖(∫ y in (0 : ℝ)..β, F (T + y * I)) - ∫ y in (0 : ℝ)..β, F (-T + y * I)‖
        ≤ ‖∫ y in (0 : ℝ)..β, F (T + y * I)‖ + ‖∫ y in (0 : ℝ)..β, F (-T + y * I)‖ :=
          norm_sub_le _ _
      _ ≤ C * Real.exp (-a * T ^ 2) * |β - 0| + C * Real.exp (-a * T ^ 2) * |β - 0| :=
          add_le_add (key T rfl) (by simpa using key (-T) (by ring))
      _ = 2 * |β| * (C * Real.exp (-a * T ^ 2)) := by rw [sub_zero]; ring
  have hVlim : Tendsto V atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall hVle)
    rw [(by ring : (0 : ℝ) = 2 * |β| * (C * 0))]
    refine (Tendsto.const_mul _ ?_).const_mul _
    refine Real.tendsto_exp_atBot.comp ?_
    have h := tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop ha)
    exact h.congr fun T => by simp [neg_mul]
  -- pass to the limit
  have h1 : Tendsto (fun T : ℝ => ∫ x in -T..T, F (x + β * I)) atTop (𝓝 (∫ x : ℝ, F (x + β * I))) :=
    intervalIntegral_tendsto_integral (hint β hβ) tendsto_neg_atTop_atBot tendsto_id
  have h2 : Tendsto (fun T : ℝ => ∫ x in -T..T, F x) atTop (𝓝 (∫ x : ℝ, F x)) := by
    have := intervalIntegral_tendsto_integral (hint 0 h0) tendsto_neg_atTop_atBot tendsto_id
    simpa using this
  refine tendsto_nhds_unique h1 ?_
  have := h2.add hVlim
  rw [add_zero] at this
  refine this.congr fun T => ?_
  exact (hC T).symm

/-- Shifting the contour of an integral over `ℝ` by a complex constant `c`. -/
theorem integral_add_eq_integral {F : ℂ → ℂ} {c : ℂ} {a C : ℝ} (ha : 0 < a)
    (hF : ∀ v : ℂ, v.im ∈ uIcc 0 c.im → DifferentiableAt ℂ F v)
    (hbound : ∀ v : ℂ, v.im ∈ uIcc 0 c.im → ‖F v‖ ≤ C * Real.exp (-a * v.re ^ 2)) :
    ∫ x : ℝ, F (x + c) = ∫ x : ℝ, F x := by
  have h1 : ∫ x : ℝ, F (x + c) = ∫ x : ℝ, F ((x + c.re : ℝ) + c.im * I) := by
    congr 1; ext x; congr 1; push_cast; rw [add_assoc, Complex.re_add_im]
  have h2 : ∫ x : ℝ, F ((x + c.re : ℝ) + c.im * I) = ∫ x : ℝ, F (x + c.im * I) :=
    integral_add_right_eq_self (fun x : ℝ => F (x + c.im * I)) c.re
  rw [h1, h2]
  exact integral_add_ofReal_mul_I_eq_integral ha hF hbound

end Complex
