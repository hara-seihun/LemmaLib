/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The Gamma integral with a complex scaling

`∫₀^∞ t^{a-1} e^{-bt} dt = b^{-a} Γ(a)` for `Re a > 0` and `Re b > 0`
(`Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`). Mathlib proves this for real `b`
(`Complex.integral_cpow_mul_exp_neg_mul_Ioi`); the complex case follows by analytic continuation
in `b` over the right half-plane, both sides being holomorphic there.
-/

public section

open Complex Real Set Filter Topology MeasureTheory

namespace Complex

theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {α β : ℝ} (hα : -1 < α) (hβ : 0 < β) :
    IntegrableOn (fun t : ℝ => t ^ α * Real.exp (-β * t)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow hα one_pos hβ
  simpa only [Real.rpow_one] using this

theorem norm_cpow_mul_exp_neg_mul {t : ℝ} (ht : 0 < t) (a b : ℂ) :
    ‖(t : ℂ) ^ (a - 1) * cexp (-(b * t))‖ = t ^ (a.re - 1) * Real.exp (-b.re * t) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, sub_re, one_re]
  congr 2
  simp [mul_comm]

theorem continuousOn_cpow_mul_exp_neg_mul (a b : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(b * t))) (Ioi 0) := by
  refine continuousOn_of_forall_continuousAt fun t ht => ?_
  exact (continuousAt_ofReal_cpow_const t (a - 1) (Or.inr (ne_of_gt ht))).mul (by fun_prop)

theorem integrableOn_cpow_mul_exp_neg_mul {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(b * t))) (Ioi 0) := by
  refine ((integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < a.re - 1) hb).mono'
    ((continuousOn_cpow_mul_exp_neg_mul a b).aestronglyMeasurable measurableSet_Ioi) ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_cpow_mul_exp_neg_mul ht]

/-- The Gamma-type integral is differentiable in the scaling parameter `b`. -/
theorem hasDerivAt_integral_cpow_mul_exp_neg_mul {a b₀ : ℂ} (ha : 0 < a.re) (hb₀ : 0 < b₀.re) :
    HasDerivAt (fun b : ℂ => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * cexp (-(b * t)))
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * (-t * cexp (-(b₀ * t)))) b₀ := by
  set ε : ℝ := b₀.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hre : ∀ b ∈ Metric.ball b₀ ε, ε ≤ b.re := by
    intro b hb
    rw [Metric.mem_ball, dist_eq_norm] at hb
    have := Complex.abs_re_le_norm (b - b₀)
    rw [sub_re] at this
    have := neg_abs_le (b.re - b₀.re)
    linarith
  have hmeas : ∀ b : ℂ, AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(b * t)))
      (volume.restrict (Ioi 0)) := fun b =>
    (continuousOn_cpow_mul_exp_neg_mul a b).aestronglyMeasurable measurableSet_Ioi
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (a - 1) * (-t * cexp (-(b₀ * t))))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun t ht => ?_
    exact (continuousAt_ofReal_cpow_const t (a - 1) (Or.inr (ne_of_gt ht))).mul (by fun_prop)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b₀ hε0)
    (Eventually.of_forall hmeas) (integrableOn_cpow_mul_exp_neg_mul ha hb₀)
    (F' := fun b (t : ℝ) => (t : ℂ) ^ (a - 1) * (-t * cexp (-(b * t)))) hmeas'
    (bound := fun t => t ^ a.re * Real.exp (-ε * t)) ?_ ?_ ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht b hb
    have hbre := hre b hb
    rw [mem_Ioi] at ht
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg ht.le, Complex.norm_exp, sub_re, one_re]
    have e : (-(b * t)).re = -b.re * t := by simp [mul_comm]
    rw [e]
    calc t ^ (a.re - 1) * (t * Real.exp (-b.re * t))
        = t ^ a.re * Real.exp (-b.re * t) := by
          rw [Real.rpow_sub_one ht.ne']; field_simp
      _ ≤ t ^ a.re * Real.exp (-ε * t) := by
          gcongr
  · exact integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hε0
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ b _
    have h1 : HasDerivAt (fun b : ℂ => -(b * t)) (-t) b := (hasDerivAt_mul_const (t : ℂ)).neg
    exact ((h1.cexp).const_mul ((t : ℂ) ^ (a - 1))).congr_deriv (by ring)

/-- `∫₀^∞ t^{a-1} e^{-bt} dt = b^{-a} Γ(a)` for `Re a > 0` and `Re b > 0`. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * cexp (-(b * t)) = b ^ (-a) * Complex.Gamma a := by
  set U : Set ℂ := {b | 0 < b.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  set F : ℂ → ℂ := fun b => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * cexp (-(b * t)) with hF
  set G : ℂ → ℂ := fun b => b ^ (-a) * Complex.Gamma a with hG
  have hFa : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hUo
    exact (hasDerivAt_integral_cpow_mul_exp_neg_mul ha hb).differentiableAt.differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hUo
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_id.cpow_const ?_).mul_const _
    exact Complex.mem_slitPlane_iff.2 (Or.inl hb)
  -- agreement on the positive reals
  have hreal : ∀ r : ℝ, 0 < r → F r = G r := by
    intro r hr
    rw [hF, hG]
    simp only
    rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hr, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
      Complex.cpow_neg]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), F z = G z := by
    have ht : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 1) := by
          have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa using h0.const_add (1 : ℝ)
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp this
        rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp]
        exact h2
      · refine Eventually.of_forall fun n => ?_
        rw [mem_compl_iff, mem_singleton_iff]
        intro h
        have h' : (1 + 1 / ((n : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine ht.frequently (Eventually.of_forall fun n => ?_).frequently
    exact hreal _ (by positivity)
  have := hFa.eqOn_of_preconnected_of_frequently_eq hGa hUc (z₀ := 1) (by simp [hU]) hfreq
  exact this hb

end Complex
