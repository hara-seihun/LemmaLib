/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

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

## Crossing a pole

`Complex.integral_div_sub_add_ofReal_mul_I_sub_integral_div_sub` is the residue theorem for the
same strip with one simple pole inside: if `N` is holomorphic on the closed strip with Gaussian
decay and `0 < Im p < β`, then

`∫ x : ℝ, N (x + β i) / (x + β i - p) - ∫ x : ℝ, N x / (x - p) = -2 π i N p`.

The proof subtracts `N p · exp (-(v - p)²) / (v - p)` to remove the pole, shifts the remaining
holomorphic function, and evaluates `∫ exp (-(x + γ)²) / (x + γ) = ∓ π i` (`Im γ ≷ 0`) by writing
`1 / (x + γ)` as a Laplace integral (`Complex.integral_exp_neg_sq_div_eq_neg_pi_I`).
-/

public section

open Complex Real Set Filter Topology MeasureTheory intervalIntegral

namespace Complex

/-- Shifting the contour of an integral over `ℝ` to the horizontal line `Im = β`, for a function
continuous on the closed strip between the two lines, holomorphic there off a countable set, and
with Gaussian decay on the strip. -/
theorem integral_add_ofReal_mul_I_eq_integral_off_countable {F : ℂ → ℂ} {β a C : ℝ} {S : Set ℂ}
    (ha : 0 < a) (hS : S.Countable)
    (hFc : ∀ v : ℂ, v.im ∈ uIcc 0 β → ContinuousAt F v)
    (hF : ∀ v : ℂ, v.im ∈ uIcc 0 β → v ∉ S → DifferentiableAt ℂ F v)
    (hbound : ∀ v : ℂ, v.im ∈ uIcc 0 β → ‖F v‖ ≤ C * Real.exp (-a * v.re ^ 2)) :
    ∫ x : ℝ, F (x + β * I) = ∫ x : ℝ, F x := by
  -- continuity and integrability along horizontal lines of the strip
  have hcont : ∀ y ∈ uIcc 0 β, Continuous fun x : ℝ => F (x + y * I) := by
    intro y hy
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h1 : ContinuousAt F (x + y * I) := hFc _ (by simpa using hy)
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
    have := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable F (-T) (T + β * I)
      S hS (by
        intro v hv
        refine (hFc v ?_).continuousWithinAt
        rw [mem_reProdIm] at hv
        simpa using hv.2) (by
        intro v hv
        rw [mem_diff, mem_reProdIm] at hv
        refine hF v ?_ hv.2
        have := hv.1.2
        simp only [neg_im, ofReal_im, neg_zero, add_im, mul_im, I_re, mul_zero, I_im, mul_one,
          zero_add, ofReal_re] at this
        rw [add_zero] at this
        exact Ioo_subset_Icc_self this)
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

/-- Shifting the contour of an integral over `ℝ` to the horizontal line `Im = β`, for a function
holomorphic on the closed strip between the two lines with Gaussian decay there. -/
theorem integral_add_ofReal_mul_I_eq_integral {F : ℂ → ℂ} {β a C : ℝ} (ha : 0 < a)
    (hF : ∀ v : ℂ, v.im ∈ uIcc 0 β → DifferentiableAt ℂ F v)
    (hbound : ∀ v : ℂ, v.im ∈ uIcc 0 β → ‖F v‖ ≤ C * Real.exp (-a * v.re ^ 2)) :
    ∫ x : ℝ, F (x + β * I) = ∫ x : ℝ, F x :=
  integral_add_ofReal_mul_I_eq_integral_off_countable (S := ∅) ha countable_empty
    (fun v hv => (hF v hv).continuousAt) (fun v hv _ => hF v hv) hbound

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

/-- `1 / w = -I ∫_0^∞ exp (I w t) dt` for `Im w > 0`. -/
theorem inv_eq_neg_I_mul_integral_exp {w : ℂ} (hw : 0 < w.im) :
    w⁻¹ = -I * ∫ t in Ioi (0 : ℝ), cexp (I * w * t) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hIw : I * w ≠ 0 := mul_ne_zero I_ne_zero hw0
  have hnorm : ∀ t : ℝ, ‖cexp (I * w * t)‖ = Real.exp (-w.im * t) := by
    intro t
    rw [Complex.norm_exp]
    congr 1
    simp [mul_comm]
  have key : ∫ t in Ioi (0 : ℝ), cexp (I * w * t) = 0 - cexp (I * w * 0) / (I * w) := by
    refine integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t : ℝ => cexp (I * w * t) / (I * w))
      ?_ ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ => cexp (I * w * t) / (I * w)).continuousWithinAt
    · intro t _
      have := ((hasDerivAt_id t).ofReal_comp.const_mul (I * w)).cexp
      have h2 := this.div_const (I * w)
      refine h2.congr_deriv ?_
      simp only [id, ofReal_one, mul_one]
      exact mul_div_cancel_right₀ _ hIw
    · refine (exp_neg_integrableOn_Ioi 0 hw).mono' ?_ ?_
      · exact (by fun_prop : Continuous fun t : ℝ => cexp (I * w * t)).aestronglyMeasurable
      · exact Eventually.of_forall fun t => (hnorm t).le
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_div, hnorm]
      rw [show (0 : ℝ) = 0 / ‖I * w‖ by simp]
      refine Tendsto.div_const ?_ _
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hw)
  rw [key]
  simp only [mul_zero, Complex.exp_zero, zero_sub]
  field_simp

theorem re_neg_sq_add_I_mul_mul {β : ℂ} (x t : ℝ) :
    (-(x + β) ^ 2 + I * (x + β) * t).re = -(x + β.re) ^ 2 + β.im ^ 2 - β.im * t := by
  simp [sq]; ring

/-- `∫ x, exp (-(x + β)²) / (x + β) = -π I` for `Im β > 0`. -/
theorem integral_exp_neg_sq_div_eq_neg_pi_I {β : ℂ} (hβ : 0 < β.im) :
    ∫ x : ℝ, cexp (-(x + β) ^ 2) / (x + β) = -π * I := by
  set f : ℝ → ℝ → ℂ := fun x t => cexp (-(x + β) ^ 2 + I * (x + β) * t) with hf
  have h1 : ∀ x : ℝ, cexp (-(x + β) ^ 2) / (x + β) = -I * ∫ t in Ioi (0 : ℝ), f x t := by
    intro x
    rw [div_eq_mul_inv, inv_eq_neg_I_mul_integral_exp (by simpa using hβ), mul_left_comm,
      ← MeasureTheory.integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hf]
    rw [← Complex.exp_add]
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul]
  have hint : Integrable (Function.uncurry f) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hg : Integrable (fun z : ℝ × ℝ =>
        (Real.exp (β.im ^ 2) * Real.exp (-1 * (z.1 + β.re) ^ 2)) * Real.exp (-β.im * z.2))
        (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
      Integrable.mul_prod (((integrable_exp_neg_mul_sq one_pos).comp_add_right β.re).const_mul _)
        (exp_neg_integrableOn_Ioi 0 hβ)
    refine hg.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact (by simp only [hf]; fun_prop : Continuous (Function.uncurry f)).aestronglyMeasurable
    · obtain ⟨x, t⟩ := z
      simp only [hf, Function.uncurry_apply_pair, Complex.norm_exp, re_neg_sq_add_I_mul_mul,
        ← Real.exp_add]
      apply le_of_eq
      congr 1
      ring
  rw [integral_integral_swap hint]
  have hinner : ∀ t : ℝ, ∫ x : ℝ, f x t = (π : ℂ) ^ (1 / 2 : ℂ) * cexp (-(1 / 4 : ℂ) * t ^ 2) := by
    intro t
    have := integral_cexp_quadratic (b := -1) (by simp) (-2 * β + I * t) (-β ^ 2 + I * β * t)
    simp only [hf]
    convert this using 2
    · ext x; congr 1; ring
    · simp
    · congr 1; linear_combination (-(t : ℂ) ^ 2 / 4) * I_sq
  simp_rw [hinner]
  rw [MeasureTheory.integral_const_mul, integral_gaussian_complex_Ioi (by norm_num)]
  have e1 : (π : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]; push_cast; rfl
  have e2 : ((π : ℂ) / (1 / 4)) ^ (1 / 2 : ℂ) = (2 * Real.sqrt π : ℂ) := by
    have : ((π : ℂ) / (1 / 4)) = ((4 * π : ℝ) : ℂ) := by push_cast; ring
    rw [this, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    push_cast; ring
  rw [e1, e2]
  have e3 : ((Real.sqrt π : ℝ) : ℂ) * ((Real.sqrt π : ℝ) : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  linear_combination (-I) * e3

theorem integrable_of_norm_le_gaussian {f : ℝ → ℂ} {a C : ℝ} (ha : 0 < a) (hf : Continuous f)
    (h : ∀ x, ‖f x‖ ≤ C * Real.exp (-a * x ^ 2)) : Integrable f :=
  ((integrable_exp_neg_mul_sq ha).const_mul C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall h)

theorem exp_neg_sub_sq_le (x c : ℝ) :
    Real.exp (-(x - c) ^ 2) ≤ Real.exp (c ^ 2) * Real.exp (-(1 / 2) * x ^ 2) := by
  rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg (x - 2 * c)]

theorem norm_exp_neg_sub_sq (v p : ℂ) :
    ‖cexp (-(v - p) ^ 2)‖ = Real.exp ((v.im - p.im) ^ 2) * Real.exp (-(v.re - p.re) ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]; congr 1; simp [sq]; ring

/-- `∫ x, exp (-(x + β)²) / (x + β) = π I` for `Im β < 0`. -/
theorem integral_exp_neg_sq_div_eq_pi_I {β : ℂ} (hβ : β.im < 0) :
    ∫ x : ℝ, cexp (-(x + β) ^ 2) / (x + β) = π * I := by
  have h := integral_exp_neg_sq_div_eq_neg_pi_I (β := (starRingEnd ℂ) β) (by simpa using hβ)
  have h2 : ∫ x : ℝ, cexp (-(x + β) ^ 2) / (x + β) =
      (starRingEnd ℂ) (∫ x : ℝ, cexp (-(x + (starRingEnd ℂ) β) ^ 2) / (x + (starRingEnd ℂ) β)) := by
    rw [← integral_conj]
    congr 1; ext x
    simp only [map_div₀, ← Complex.exp_conj, map_neg, map_pow, map_add, Complex.conj_ofReal,
      Complex.conj_conj]
  rw [h2, h]
  simp

/-- Crossing a simple pole. If `N` is holomorphic on the closed strip `0 ≤ Im v ≤ β` with Gaussian
decay there, and `0 < Im p < β`, then
`∫ N (x + β I) / (x + β I - p) - ∫ N x / (x - p) = -2 π I N p`. -/
theorem integral_div_sub_add_ofReal_mul_I_sub_integral_div_sub {N : ℂ → ℂ} {p : ℂ} {β a C : ℝ}
    (ha : 0 < a) (hp0 : 0 < p.im) (hpβ : p.im < β)
    (hN : ∀ v : ℂ, v.im ∈ Icc 0 β → DifferentiableAt ℂ N v)
    (hbound : ∀ v : ℂ, v.im ∈ Icc 0 β → ‖N v‖ ≤ C * Real.exp (-a * v.re ^ 2)) :
    (∫ x : ℝ, N (x + β * I) / (x + β * I - p)) - ∫ x : ℝ, N x / (x - p) = -2 * π * I * N p := by
  have hβ : 0 < β := hp0.trans hpβ
  have hC : 0 ≤ C := by
    have := hbound 0 (by simp [hβ.le])
    simp only [zero_re, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  set φ : ℂ → ℂ := fun v => cexp (-(v - p) ^ 2) with hφ
  set H : ℂ → ℂ := fun v => N v - N p * φ v with hH
  have hHp : H p = 0 := by simp [hH, hφ]
  have hHdiff : ∀ v : ℂ, v.im ∈ Icc 0 β → DifferentiableAt ℂ H v := fun v hv =>
    (hN v hv).sub ((differentiableAt_const _).mul (by simp only [hφ]; fun_prop))
  set G := dslope H p with hG
  have hGne : ∀ v, v ≠ p → G v = H v / (v - p) := fun v hv => by
    rw [hG, dslope_of_ne _ hv, slope_def_field, hHp, sub_zero]
  set δ : ℝ := min p.im (β - p.im) / 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; have := lt_min hp0 (sub_pos.2 hpβ); positivity
  have hδ1 : δ < p.im := by rw [hδ]; have := min_le_left p.im (β - p.im); linarith
  have hδ2 : δ < β - p.im := by rw [hδ]; have := min_le_right p.im (β - p.im); linarith
  have hball : ∀ v ∈ Metric.closedBall p δ, v.im ∈ Icc 0 β := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at hv
    have := (abs_im_le_norm (v - p)).trans hv
    rw [sub_im, abs_le] at this
    constructor <;> linarith
  have hGdiff : ∀ v : ℂ, v.im ∈ Icc 0 β → DifferentiableAt ℂ G v := by
    intro v hv
    by_cases hvp : v = p
    · subst hvp
      have : DifferentiableOn ℂ H (Metric.ball v δ) := fun w hw =>
        (hHdiff w (hball w (Metric.ball_subset_closedBall hw))).differentiableWithinAt
      exact ((differentiableOn_dslope (Metric.ball_mem_nhds v hδpos)).2 this).differentiableAt
        (Metric.ball_mem_nhds v hδpos)
    · exact (differentiableAt_dslope_of_ne hvp).2 (hHdiff v hv)
  -- a Gaussian bound for `G` on the strip
  obtain ⟨M, hM⟩ := (isCompact_closedBall p δ).exists_bound_of_continuousOn
    (fun v hv => (hGdiff v (hball v hv)).continuousAt.continuousWithinAt)
  set a' : ℝ := min a (1 / 2) with ha'
  have ha'pos : 0 < a' := lt_min ha (by norm_num)
  set C₁ : ℝ := (C + ‖N p‖ * Real.exp (β ^ 2) * Real.exp (p.re ^ 2)) / δ with hC₁
  set C₂ : ℝ := max C₁ (max M 0 * Real.exp (a' * (|p.re| + δ) ^ 2)) with hC₂
  have hGbound : ∀ v : ℂ, v.im ∈ Icc 0 β → ‖G v‖ ≤ C₂ * Real.exp (-a' * v.re ^ 2) := by
    intro v hv
    have hexp_pos : 0 < Real.exp (-a' * v.re ^ 2) := Real.exp_pos _
    by_cases hvb : v ∈ Metric.closedBall p δ
    · -- inside the ball: use the compactness bound
      have h1 : ‖G v‖ ≤ max M 0 := (hM v hvb).trans (le_max_left _ _)
      have h2 : v.re ^ 2 ≤ (|p.re| + δ) ^ 2 := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hvb
        have := (abs_re_le_norm (v - p)).trans hvb
        rw [sub_re] at this
        have h3 : |v.re| ≤ |p.re| + δ := by
          calc |v.re| = |(v.re - p.re) + p.re| := by ring_nf
            _ ≤ |v.re - p.re| + |p.re| := abs_add_le _ _
            _ ≤ |p.re| + δ := by linarith
        calc v.re ^ 2 = |v.re| ^ 2 := (sq_abs _).symm
          _ ≤ (|p.re| + δ) ^ 2 := by gcongr
      have h4 : 1 ≤ Real.exp (a' * (|p.re| + δ) ^ 2) * Real.exp (-a' * v.re ^ 2) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]; nlinarith
      calc ‖G v‖ ≤ max M 0 := h1
        _ = max M 0 * 1 := (mul_one _).symm
        _ ≤ max M 0 * (Real.exp (a' * (|p.re| + δ) ^ 2) * Real.exp (-a' * v.re ^ 2)) := by
          gcongr
        _ = (max M 0 * Real.exp (a' * (|p.re| + δ) ^ 2)) * Real.exp (-a' * v.re ^ 2) := by ring
        _ ≤ C₂ * Real.exp (-a' * v.re ^ 2) := by gcongr; exact le_max_right _ _
    · -- outside the ball
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hvb
      have hvp : v ≠ p := fun h => by rw [h, sub_self, norm_zero] at hvb; linarith
      rw [hGne v hvp, norm_div]
      have hHb : ‖H v‖ ≤ (C + ‖N p‖ * Real.exp (β ^ 2) * Real.exp (p.re ^ 2)) *
          Real.exp (-a' * v.re ^ 2) := by
        have e1 : Real.exp (-a * v.re ^ 2) ≤ Real.exp (-a' * v.re ^ 2) := by
          apply Real.exp_le_exp.2
          have := min_le_left a (1 / 2)
          nlinarith [sq_nonneg v.re]
        have e2 : ‖φ v‖ ≤ Real.exp (β ^ 2) * Real.exp (p.re ^ 2) * Real.exp (-a' * v.re ^ 2) := by
          simp only [hφ]
          rw [norm_exp_neg_sub_sq]
          have e3 : Real.exp ((v.im - p.im) ^ 2) ≤ Real.exp (β ^ 2) := by
            apply Real.exp_le_exp.2
            obtain ⟨h1, h2⟩ := hv
            nlinarith
          have e4 : Real.exp (-(v.re - p.re) ^ 2) ≤ Real.exp (p.re ^ 2) * Real.exp (-a' * v.re ^ 2) := by
            refine (exp_neg_sub_sq_le v.re p.re).trans ?_
            gcongr
            have := min_le_right a (1 / 2)
            nlinarith [sq_nonneg v.re]
          calc Real.exp ((v.im - p.im) ^ 2) * Real.exp (-(v.re - p.re) ^ 2)
              ≤ Real.exp (β ^ 2) * (Real.exp (p.re ^ 2) * Real.exp (-a' * v.re ^ 2)) := by gcongr
            _ = _ := by ring
        calc ‖H v‖ = ‖N v - N p * φ v‖ := rfl
          _ ≤ ‖N v‖ + ‖N p‖ * ‖φ v‖ := by rw [← norm_mul]; exact norm_sub_le _ _
          _ ≤ C * Real.exp (-a' * v.re ^ 2) +
              ‖N p‖ * (Real.exp (β ^ 2) * Real.exp (p.re ^ 2) * Real.exp (-a' * v.re ^ 2)) := by
            gcongr
            exact (hbound v hv).trans (by gcongr)
          _ = _ := by ring
      calc ‖H v‖ / ‖v - p‖ ≤ ‖H v‖ / δ := by gcongr
        _ ≤ (C + ‖N p‖ * Real.exp (β ^ 2) * Real.exp (p.re ^ 2)) * Real.exp (-a' * v.re ^ 2) / δ := by
          gcongr
        _ = C₁ * Real.exp (-a' * v.re ^ 2) := by rw [hC₁]; ring
        _ ≤ C₂ * Real.exp (-a' * v.re ^ 2) := by gcongr; exact le_max_left _ _
  -- shift the contour of `G`
  have hshift : ∫ x : ℝ, G (x + β * I) = ∫ x : ℝ, G x :=
    integral_add_ofReal_mul_I_eq_integral ha'pos
      (fun v hv => hGdiff v (by rwa [uIcc_of_le hβ.le] at hv))
      (fun v hv => hGbound v (by rwa [uIcc_of_le hβ.le] at hv))
  -- split the integrals of `G` on the two lines
  have hne_top : ∀ x : ℝ, (x : ℂ) + β * I ≠ p := fun x h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hne_bot : ∀ x : ℝ, (x : ℂ) ≠ p := fun x h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hnorm_top : ∀ x : ℝ, β - p.im ≤ ‖(x : ℂ) + β * I - p‖ := fun x => by
    have := abs_im_le_norm ((x : ℂ) + β * I - p)
    simpa [abs_of_pos (sub_pos.2 hpβ)] using this
  have hnorm_bot : ∀ x : ℝ, p.im ≤ ‖(x : ℂ) - p‖ := fun x => by
    have := abs_im_le_norm ((x : ℂ) - p)
    simpa [abs_of_pos hp0] using this
  have hmem_top : ∀ x : ℝ, ((x : ℂ) + β * I).im ∈ Icc 0 β := fun x => by simp [hβ.le]
  have hmem_bot : ∀ x : ℝ, ((x : ℂ)).im ∈ Icc 0 β := fun x => by simp [hβ.le]
  have hφbound : ∀ v : ℂ, v.im ∈ Icc 0 β →
      ‖φ v‖ ≤ Real.exp (β ^ 2) * Real.exp (p.re ^ 2) * Real.exp (-(1 / 2) * v.re ^ 2) := by
    intro v hv
    simp only [hφ]
    rw [norm_exp_neg_sub_sq]
    have e3 : Real.exp ((v.im - p.im) ^ 2) ≤ Real.exp (β ^ 2) := by
      apply Real.exp_le_exp.2
      obtain ⟨h1, h2⟩ := hv
      nlinarith
    calc Real.exp ((v.im - p.im) ^ 2) * Real.exp (-(v.re - p.re) ^ 2)
        ≤ Real.exp (β ^ 2) * (Real.exp (p.re ^ 2) * Real.exp (-(1 / 2) * v.re ^ 2)) :=
          mul_le_mul e3 (exp_neg_sub_sq_le v.re p.re) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = _ := by ring
  have hcN_top : Continuous fun x : ℝ => N ((x : ℂ) + β * I) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h1 : ContinuousAt N ((x : ℂ) + β * I) := (hN _ (hmem_top x)).continuousAt
    exact h1.comp (f := fun x : ℝ => (x : ℂ) + β * I) (by fun_prop)
  have hcN_bot : Continuous fun x : ℝ => N (x : ℂ) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h1 : ContinuousAt N (x : ℂ) := (hN _ (hmem_bot x)).continuousAt
    exact h1.comp (f := fun x : ℝ => (x : ℂ)) (by fun_prop)
  have hint_top_N : Integrable fun x : ℝ => N (x + β * I) / (x + β * I - p) := by
    refine integrable_of_norm_le_gaussian ha (C := C / (β - p.im)) ?_ fun x => ?_
    · exact hcN_top.div (by fun_prop) fun x => sub_ne_zero.2 (hne_top x)
    · rw [norm_div, div_mul_eq_mul_div]
      exact div_le_div₀ (by positivity) (by simpa using hbound _ (hmem_top x)) (sub_pos.2 hpβ)
        (hnorm_top x)
  have hint_bot_N : Integrable fun x : ℝ => N x / (x - p) := by
    refine integrable_of_norm_le_gaussian ha (C := C / p.im) ?_ fun x => ?_
    · exact hcN_bot.div (by fun_prop) fun x => sub_ne_zero.2 (hne_bot x)
    · rw [norm_div, div_mul_eq_mul_div]
      exact div_le_div₀ (by positivity) (by simpa using hbound _ (hmem_bot x)) hp0 (hnorm_bot x)
  have hint_top_φ : Integrable fun x : ℝ => φ (x + β * I) / (x + β * I - p) := by
    refine integrable_of_norm_le_gaussian (a := 1 / 2) (by norm_num)
      (C := Real.exp (β ^ 2) * Real.exp (p.re ^ 2) / (β - p.im)) ?_ fun x => ?_
    · simp only [hφ]
      exact Continuous.div (by fun_prop) (by fun_prop) fun x => sub_ne_zero.2 (hne_top x)
    · rw [norm_div, div_mul_eq_mul_div]
      exact div_le_div₀ (by positivity) (by simpa using hφbound _ (hmem_top x)) (sub_pos.2 hpβ)
        (hnorm_top x)
  have hint_bot_φ : Integrable fun x : ℝ => φ x / (x - p) := by
    refine integrable_of_norm_le_gaussian (a := 1 / 2) (by norm_num)
      (C := Real.exp (β ^ 2) * Real.exp (p.re ^ 2) / p.im) ?_ fun x => ?_
    · simp only [hφ]
      exact Continuous.div (by fun_prop) (by fun_prop) fun x => sub_ne_zero.2 (hne_bot x)
    · rw [norm_div, div_mul_eq_mul_div]
      exact div_le_div₀ (by positivity) (by simpa using hφbound _ (hmem_bot x)) hp0 (hnorm_bot x)
  have htop : ∫ x : ℝ, G (x + β * I) =
      (∫ x : ℝ, N (x + β * I) / (x + β * I - p)) -
        N p * ∫ x : ℝ, φ (x + β * I) / (x + β * I - p) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub hint_top_N (hint_top_φ.const_mul _)]
    congr 1; ext x
    rw [hGne _ (hne_top x)]
    simp only [hH]
    ring
  have hbot : ∫ x : ℝ, G x = (∫ x : ℝ, N x / (x - p)) - N p * ∫ x : ℝ, φ x / (x - p) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub hint_bot_N (hint_bot_φ.const_mul _)]
    congr 1; ext x
    rw [hGne _ (hne_bot x)]
    simp only [hH]
    ring
  have hΨtop : ∫ x : ℝ, φ (x + β * I) / (x + β * I - p) = -π * I := by
    have := integral_exp_neg_sq_div_eq_neg_pi_I (β := β * I - p) (by simp; linarith)
    rw [← this]
    congr 1; ext x
    simp only [hφ]
    rw [add_sub_assoc]
  have hΨbot : ∫ x : ℝ, φ x / (x - p) = π * I := by
    have := integral_exp_neg_sq_div_eq_pi_I (β := -p) (by simp; linarith)
    rw [← this]
    congr 1
  rw [htop, hbot, hΨtop, hΨbot] at hshift
  linear_combination hshift

/-- The residue theorem for the strip `β ≤ Im v ≤ 0` with `β < 0`: crossing the pole from below
reverses the sign. -/
theorem integral_div_sub_add_ofReal_mul_I_sub_integral_div_sub_of_neg {N : ℂ → ℂ} {p : ℂ}
    {β a C : ℝ} (ha : 0 < a) (hβp : β < p.im) (hp0 : p.im < 0)
    (hN : ∀ v : ℂ, v.im ∈ Icc β 0 → DifferentiableAt ℂ N v)
    (hbound : ∀ v : ℂ, v.im ∈ Icc β 0 → ‖N v‖ ≤ C * Real.exp (-a * v.re ^ 2)) :
    (∫ x : ℝ, N (x + β * I) / (x + β * I - p)) - ∫ x : ℝ, N x / (x - p) = 2 * π * I * N p := by
  have key := integral_div_sub_add_ofReal_mul_I_sub_integral_div_sub (N := fun v => N (v + β * I))
    (p := p - β * I) (β := -β) (a := a) (C := C) ha (by simp; linarith) (by simp; linarith)
    (fun v hv => by
      refine (hN (v + β * I) ?_).comp v ((differentiableAt_id).add_const _)
      simp at hv ⊢; constructor <;> linarith [hv.1, hv.2])
    (fun v hv => by
      have := hbound (v + β * I) (by simp at hv ⊢; constructor <;> linarith [hv.1, hv.2])
      simpa using this)
  have e1 : (fun x : ℝ => N ((x : ℂ) + ((-β : ℝ) : ℂ) * I + β * I) /
      ((x : ℂ) + ((-β : ℝ) : ℂ) * I - (p - β * I))) = fun x : ℝ => N x / (x - p) := by
    ext x; push_cast
    rw [show (x : ℂ) + -(β : ℂ) * I + β * I = x by ring,
      show (x : ℂ) + -(β : ℂ) * I - (p - β * I) = x - p by ring]
  have e2 : (fun x : ℝ => N ((x : ℂ) + β * I) / ((x : ℂ) - (p - β * I))) =
      fun x : ℝ => N (x + β * I) / (x + β * I - p) := by
    ext x; rw [show (x : ℂ) - (p - β * I) = x + β * I - p by ring]
  rw [e1, e2, show p - β * I + β * I = p by ring] at key
  linear_combination -key

end Complex
