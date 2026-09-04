/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.RiemannSiegel.Mellin
public import LemmaLib.Analysis.Complex.ContourShift

/-!
# The reflected Riemann–Siegel integral as a Gaussian integral

For `Re s > 2` and `0 < c < 1`, the complex conjugate of the Riemann–Siegel integral at `1 - s̄`
is a multiple of the Gaussian integral `I₀(s)` of `LemmaLib.NumberTheory.RiemannSiegel.Mellin`:
`conj (R(1 - s̄, c)) = e^{-iπs/4} (1 + e^{iπs}) I₀(s)` (`RiemannSiegel.conj_rsIntegral_one_sub`).

Conjugation turns the contour `c - ωx` into `c - ω̄x`, and the integrand into
`u^{s-1} e^{-iπu²} / (e^{iπu} - e^{-iπu})` (`foldIntegrand`). For `Re s > 2` this integrand
extends continuously by `0` to the origin, so the contour can be moved to the parallel line through
`0`; it then folds into the two rays `ω̄ (0, ∞)` and `-ω̄ (0, ∞)`, on each of which the integrand
is a multiple of the integrand of `I₀(s)`.
-/

public section

open Complex Real Set Filter Topology MeasureTheory

local notation "ω" => Complex.rsOmega

namespace RiemannSiegel

/-- The reflected Riemann–Siegel integrand `u^{s-1} e^{-iπu²} / (e^{iπu} - e^{-iπu})`. -/
@[expose] noncomputable def foldIntegrand (s u : ℂ) : ℂ :=
  u ^ (s - 1) * (cexp (-(π * I * u ^ 2)) / (cexp (π * I * u) - cexp (-(π * I * u))))

/-! ### Conjugating the Riemann–Siegel integral -/

theorem conj_integrand_conj {s u : ℂ} (hu : arg u ≠ π) :
    (starRingEnd ℂ) (integrand (1 - (starRingEnd ℂ) s) ((starRingEnd ℂ) u)) =
      -foldIntegrand s u := by
  unfold integrand kernel foldIntegrand
  have h1 : ((starRingEnd ℂ) u) ^ (-(1 - (starRingEnd ℂ) s)) = (starRingEnd ℂ) (u ^ (s - 1)) := by
    rw [show -(1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (s - 1) by rw [map_sub, map_one]; ring,
      Complex.conj_cpow _ _ hu, Complex.conj_conj]
  rw [h1, map_mul, Complex.conj_conj, map_div₀, map_sub, ← Complex.exp_conj, ← Complex.exp_conj,
    ← Complex.exp_conj]
  simp only [map_mul, map_neg, map_pow, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
  rw [show (π : ℂ) * -I * u ^ 2 = -(π * I * u ^ 2) by ring,
    show (π : ℂ) * -I * u = -(π * I * u) by ring, neg_neg,
    show cexp (-(π * I * u)) - cexp (π * I * u) = -(cexp (π * I * u) - cexp (-(π * I * u))) by ring,
    div_neg, ← neg_sub]
  ring

theorem arg_line_conj_ne_pi {c : ℝ} (hc0 : 0 < c) (x : ℝ) :
    arg ((c : ℂ) - (starRingEnd ℂ) ω * x) ≠ π := by
  rw [Ne, Complex.arg_eq_pi_iff, not_and]
  intro hre him
  rw [sub_im, Complex.im_mul_ofReal, conj_rsOmega_im, ofReal_im] at him
  have hx : x = 0 := by
    have : Real.sqrt 2 / 2 * x = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exfalso; have : 0 < Real.sqrt 2 / 2 := by positivity
      linarith
    · exact h
  rw [hx, sub_re, Complex.re_mul_ofReal, ofReal_re] at hre
  simp at hre
  linarith

theorem conj_line_eq (c x : ℝ) :
    (c : ℂ) - ω * x = (starRingEnd ℂ) ((c : ℂ) - (starRingEnd ℂ) ω * x) := by
  simp [map_sub, map_mul, Complex.conj_ofReal]

/-- `conj (R(1 - s̄, c)) = ∫ ω̄ foldIntegrand s (c - ω̄ x) dx`. -/
theorem conj_rsIntegral_one_sub_eq_integral (s : ℂ) {c : ℝ} (hc0 : 0 < c) :
    (starRingEnd ℂ) (rsIntegral (1 - (starRingEnd ℂ) s) c) =
      ∫ x : ℝ, (starRingEnd ℂ) ω * foldIntegrand s ((c : ℂ) - (starRingEnd ℂ) ω * x) := by
  unfold rsIntegral
  rw [← integral_conj]
  congr 1
  ext x
  rw [map_mul, map_neg, conj_line_eq, conj_integrand_conj (arg_line_conj_ne_pi hc0 x)]
  ring

/-- The line `c - ω̄ x` is `ω̄ ((β - x) + β i)` with `β = c √2 / 2`. -/
theorem line_conj_eq_conj_rsOmega_mul (c x : ℝ) :
    (c : ℂ) - (starRingEnd ℂ) ω * x =
      (starRingEnd ℂ) ω * (((c * (Real.sqrt 2 / 2) - x : ℝ) : ℂ) + (c * (Real.sqrt 2 / 2) : ℝ) * I) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext
  · simp [rsOmega_re, rsOmega_im]
    linear_combination (-(c / 2)) * h2
  · simp [rsOmega_re, rsOmega_im]
    nlinarith

/-- `conj (R(1 - s̄, c)) = ω̄ ∫ F (x + β i) dx` with `F v = foldIntegrand s (ω̄ v)`, `β = c √2 / 2`. -/
theorem conj_rsIntegral_one_sub_eq_integral_line (s : ℂ) {c : ℝ} (hc0 : 0 < c) :
    (starRingEnd ℂ) (rsIntegral (1 - (starRingEnd ℂ) s) c) =
      (starRingEnd ℂ) ω * ∫ x : ℝ,
        foldIntegrand s ((starRingEnd ℂ) ω * (x + (c * (Real.sqrt 2 / 2) : ℝ) * I)) := by
  rw [conj_rsIntegral_one_sub_eq_integral s hc0, integral_const_mul]
  congr 1
  rw [← integral_sub_left_eq_self
    (fun x : ℝ => foldIntegrand s ((starRingEnd ℂ) ω * (x + (c * (Real.sqrt 2 / 2) : ℝ) * I)))
    volume (c * (Real.sqrt 2 / 2))]
  congr 1
  ext x
  rw [line_conj_eq_conj_rsOmega_mul]

/-! ### Bounds on the reflected integrand -/

theorem abs_re_add_im_le_sqrt_two_mul_norm (u : ℂ) : |u.re + u.im| ≤ Real.sqrt 2 * ‖u‖ := by
  have := abs_re_sub_im_le_sqrt_two_mul_norm ((starRingEnd ℂ) u)
  rwa [Complex.conj_re, Complex.conj_im, sub_neg_eq_add, Complex.norm_conj] at this

/-- `‖(e^{iπu} - e^{-iπu})⁻¹‖ ≤ 1 / (4 ‖u‖)` for `‖u‖ ≤ 1/2`. -/
theorem norm_inv_exp_sub_exp_neg_le_of_norm_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖(cexp (π * I * u) - cexp (-(π * I * u)))⁻¹‖ ≤ 1 / (4 * ‖u‖) := by
  rw [exp_sub_exp_neg_eq_two_I_sin, norm_inv, norm_mul, norm_mul, Complex.norm_two,
    Complex.norm_I, mul_one]
  have h := two_mul_norm_sub_le_norm_sin_pi_mul u 0 (by
    rw [Int.cast_zero, sub_zero]; exact (Complex.abs_re_le_norm u).trans hu)
  rw [Int.cast_zero, sub_zero] at h
  rcases eq_or_ne u 0 with rfl | hu0
  · simp
  · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
    rw [one_div]
    exact inv_anti₀ (by positivity) (by linarith)

/-- `‖(e^{iπu} - e^{-iπu})⁻¹‖ ≤ 1 / (4 ‖u‖) + √2 / (4 (1 - c))` on the strip
`0 ≤ Re u + Im u ≤ c`. -/
theorem norm_inv_exp_sub_exp_neg_le_of_fold_strip {u : ℂ} {c : ℝ} (hc1 : c < 1)
    (hu : u.re + u.im ∈ Icc 0 c) :
    ‖(cexp (π * I * u) - cexp (-(π * I * u)))⁻¹‖ ≤
      1 / (4 * ‖u‖) + Real.sqrt 2 / (4 * (1 - c)) := by
  have hc' : 0 < 1 - c := by linarith
  have hpos1 : 0 ≤ 1 / (4 * ‖u‖) := by positivity
  have hpos2 : 0 ≤ Real.sqrt 2 / (4 * (1 - c)) := by positivity
  rw [exp_sub_exp_neg_eq_two_I_sin, norm_inv, norm_mul, norm_mul, Complex.norm_two,
    Complex.norm_I, mul_one]
  set m : ℤ := round u.re with hm
  have h := two_mul_norm_sub_le_norm_sin_pi_mul u m (abs_sub_round u.re)
  rcases eq_or_ne m 0 with hm0 | hm0
  · rw [hm0, Int.cast_zero, sub_zero] at h
    rcases eq_or_ne u 0 with rfl | hu0
    · simp; positivity
    · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
      refine le_trans ?_ (le_add_of_nonneg_right hpos2)
      rw [one_div]
      exact inv_anti₀ (by positivity) (by linarith)
  · have hκ : 1 - c ≤ |u.re + u.im - m| := by
      rcases lt_or_gt_of_ne hm0 with hneg | hpos
      · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.2 hneg
        rw [abs_of_nonneg (by linarith [hu.1])]
        linarith [hu.1, hu.2]
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
        rw [abs_of_nonpos (by linarith [hu.2])]
        linarith [hu.1, hu.2]
    have h2 : 1 - c ≤ Real.sqrt 2 * ‖u - m‖ := by
      refine hκ.trans ?_
      have := abs_re_add_im_le_sqrt_two_mul_norm (u - m)
      rw [sub_re, sub_im, Complex.intCast_re, Complex.intCast_im, sub_zero] at this
      rw [add_sub_right_comm]
      exact this
    refine le_trans ?_ (le_add_of_nonneg_left hpos1)
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hsin : 0 < ‖Complex.sin (π * u)‖ := by nlinarith
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem norm_cpow_sub_one_le (u s : ℂ) :
    ‖u ^ (s - 1)‖ ≤ ‖u‖ ^ (s.re - 1) * Real.exp (π * |s.im|) := by
  refine (Complex.norm_cpow_le u (s - 1)).trans ?_
  rw [sub_re, one_re, sub_im, one_im, sub_zero, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  calc -(arg u * s.im) ≤ |arg u * s.im| := neg_le_abs _
    _ = |arg u| * |s.im| := abs_mul _ _
    _ ≤ π * |s.im| := by gcongr; exact Complex.abs_arg_le_pi u

theorem norm_exp_neg_pi_I_mul_sq (u : ℂ) :
    ‖cexp (-(π * I * u ^ 2))‖ = Real.exp (2 * π * u.re * u.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq, Complex.mul_re, Complex.mul_im]
  ring

theorem re_add_im_conj_rsOmega_mul (v : ℂ) :
    ((starRingEnd ℂ) ω * v).re + ((starRingEnd ℂ) ω * v).im = Real.sqrt 2 * v.im := by
  simp [Complex.mul_re, Complex.mul_im, rsOmega_re, rsOmega_im]
  ring

theorem two_mul_re_mul_im_conj_rsOmega_mul (v : ℂ) :
    2 * ((starRingEnd ℂ) ω * v).re * ((starRingEnd ℂ) ω * v).im = v.im ^ 2 - v.re ^ 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp [Complex.mul_re, Complex.mul_im, rsOmega_re, rsOmega_im]
  linear_combination ((v.im ^ 2 - v.re ^ 2) / 2) * h2

theorem foldIntegrand_zero {s : ℂ} (hs : s ≠ 1) : foldIntegrand s 0 = 0 := by
  unfold foldIntegrand
  rw [Complex.zero_cpow (sub_ne_zero.2 hs), zero_mul]

/-- The bound on the reflected integrand on the strip `0 ≤ Im v ≤ c √2 / 2`, `v = ω u`. -/
theorem norm_foldIntegrand_conj_rsOmega_mul_le {s : ℂ} (hs : 2 ≤ s.re) {c : ℝ} (hc1 : c < 1)
    {v : ℂ} (hv : v.im ∈ Icc 0 (c * (Real.sqrt 2 / 2))) :
    ‖foldIntegrand s ((starRingEnd ℂ) ω * v)‖ ≤
      Real.exp (π * |s.im|) * Real.exp (π * (v.im ^ 2 - v.re ^ 2)) *
        (‖v‖ ^ (s.re - 2) / 4 + Real.sqrt 2 / (4 * (1 - c)) * ‖v‖ ^ (s.re - 1)) := by
  have hc' : 0 < 1 - c := by linarith
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [mul_zero, foldIntegrand_zero (fun h => by rw [h] at hs; norm_num at hs), norm_zero]
    positivity
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hstrip : ((starRingEnd ℂ) ω * v).re + ((starRingEnd ℂ) ω * v).im ∈ Icc 0 c := by
    rw [re_add_im_conj_rsOmega_mul]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    constructor
    · have := hv.1; positivity
    · have := hv.2
      have hs2 : 0 < Real.sqrt 2 := by positivity
      nlinarith
  unfold foldIntegrand
  rw [norm_mul, div_eq_mul_inv, norm_mul, norm_exp_neg_pi_I_mul_sq,
    show 2 * π * ((starRingEnd ℂ) ω * v).re * ((starRingEnd ℂ) ω * v).im =
      π * (2 * ((starRingEnd ℂ) ω * v).re * ((starRingEnd ℂ) ω * v).im) by ring,
    two_mul_re_mul_im_conj_rsOmega_mul]
  have h1 := norm_cpow_sub_one_le ((starRingEnd ℂ) ω * v) s
  rw [norm_mul, norm_conj_rsOmega, one_mul] at h1
  have h3 := norm_inv_exp_sub_exp_neg_le_of_fold_strip hc1 hstrip
  rw [norm_mul, norm_conj_rsOmega, one_mul] at h3
  calc ‖((starRingEnd ℂ) ω * v) ^ (s - 1)‖ * (Real.exp (π * (v.im ^ 2 - v.re ^ 2)) *
        ‖(cexp (π * I * ((starRingEnd ℂ) ω * v)) - cexp (-(π * I * ((starRingEnd ℂ) ω * v))))⁻¹‖)
      ≤ ‖v‖ ^ (s.re - 1) * Real.exp (π * |s.im|) * (Real.exp (π * (v.im ^ 2 - v.re ^ 2)) *
          (1 / (4 * ‖v‖) + Real.sqrt 2 / (4 * (1 - c)))) := by
        gcongr
    _ = Real.exp (π * |s.im|) * Real.exp (π * (v.im ^ 2 - v.re ^ 2)) *
        (‖v‖ ^ (s.re - 2) / 4 + Real.sqrt 2 / (4 * (1 - c)) * ‖v‖ ^ (s.re - 1)) := by
        rw [Real.rpow_sub hn s.re 2, Real.rpow_sub hn s.re 1, Real.rpow_one, Real.rpow_two]
        field_simp

end RiemannSiegel
