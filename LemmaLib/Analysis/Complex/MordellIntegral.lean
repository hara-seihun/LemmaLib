/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.Analysis.Complex.ContourShift
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Mordell integral along Riemann–Siegel lines

This file defines the Mordell integral
`mordell τ z c = ∫ exp (π i τ u² + 2 π i u z) / (exp (π i u) - exp (-π i u)) du`
along the line `u = c - ω x` (`x : ℝ`) through the real point `c`, where `ω = exp (π i / 4)`,
for `Re τ > 0`, and proves its two functional equations:

* `mordell_add_one`: `mordell τ (z + 1) c = mordell τ z c + (Gaussian integral)`,
* `mordell_eq_mordell_sub_one_sub_one`: for `0 < c < 1`,
  `mordell τ z c = mordell τ z (c - 1) - 1`, the residue of the pole at `u = 0`.

These are the ingredients of Siegel's derivation of the Riemann–Siegel integral formula.

## Main definitions

* `Complex.rsOmega`: `ω = exp (π i / 4)`.
* `Complex.sincPi`: `sin (π u) / u` with the removable singularity filled in.
* `Complex.mordellExponent`, `Complex.mordellIntegrand`, `Complex.mordell`.

## Main results

* `Complex.two_mul_norm_sub_le_norm_sin_pi_mul`: `|sin (π u)| ≥ 2 |u - m|` when `m` is the
  nearest integer to `Re u`.
* `Complex.integrable_mordellIntegrand_line`: the integrand is integrable along every line
  `c - ω x` with `c` not an integer.
* `Complex.mordell_add_one`, `Complex.mordell_eq_mordell_sub_one_sub_one`.
-/

public section

open Complex Real Set Filter Topology MeasureTheory

/-- The Riemann–Siegel direction `ω = exp (π i / 4)`. -/
@[expose] noncomputable def Complex.rsOmega : ℂ := cexp (π * I / 4)
local notation "ω" => Complex.rsOmega

namespace Complex

theorem rsOmega_eq : ω = ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * I := by
  rw [rsOmega, show (π : ℂ) * I / 4 = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]

theorem rsOmega_re : (ω : ℂ).re = Real.sqrt 2 / 2 := by rw [rsOmega_eq]; simp
theorem rsOmega_im : (ω : ℂ).im = Real.sqrt 2 / 2 := by rw [rsOmega_eq]; simp
theorem conj_rsOmega_re : ((starRingEnd ℂ) ω).re = Real.sqrt 2 / 2 := by
  rw [conj_re, rsOmega_re]
theorem conj_rsOmega_im : ((starRingEnd ℂ) ω).im = -(Real.sqrt 2 / 2) := by
  rw [conj_im, rsOmega_im]

theorem sqrt_two_div_two_sq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem rsOmega_sq : ω ^ 2 = I := by
  apply Complex.ext
  · simp [sq, rsOmega_re, rsOmega_im]
  · simp [sq, rsOmega_re, rsOmega_im]; nlinarith [sqrt_two_div_two_sq]

theorem norm_rsOmega : ‖ω‖ = 1 := by
  rw [rsOmega, show (π : ℂ) * I / 4 = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I]

theorem rsOmega_ne_zero : ω ≠ 0 := by
  intro h; have := norm_rsOmega; rw [h, norm_zero] at this; exact zero_ne_one this

theorem conj_rsOmega_mul : (starRingEnd ℂ) ω * ω = 1 := by
  rw [mul_comm, Complex.mul_conj, normSq_eq_norm_sq, norm_rsOmega]; simp

theorem norm_conj_rsOmega : ‖(starRingEnd ℂ) ω‖ = 1 := by rw [Complex.norm_conj, norm_rsOmega]

theorem norm_sub_ge_abs_im_mul_conj_rsOmega (u : ℂ) (n : ℝ) :
    |(u * (starRingEnd ℂ) ω).im + n * (Real.sqrt 2 / 2)| ≤ ‖u - n‖ := by
  have e : (u * (starRingEnd ℂ) ω).im + n * (Real.sqrt 2 / 2) = ((u - n) * (starRingEnd ℂ) ω).im := by
    rw [sub_mul, sub_im, Complex.im_ofReal_mul, conj_rsOmega_im]; ring
  rw [e]
  refine (abs_im_le_norm _).trans ?_
  rw [norm_mul, norm_conj_rsOmega, mul_one]

/-! ### The complex sine near the integers -/

theorem norm_sin_pi_mul_sq (u : ℂ) :
    ‖Complex.sin (π * u)‖ ^ 2 = Real.sin (π * u.re) ^ 2 + Real.sinh (π * u.im) ^ 2 := by
  have e : (π : ℂ) * u = ((π * u.re : ℝ) : ℂ) + ((π * u.im : ℝ) : ℂ) * I := by
    push_cast; conv_lhs => rw [← Complex.re_add_im u]
    ring
  rw [e, Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_im, mul_im]
  have h1 := Real.sin_sq_add_cos_sq (π * u.re)
  have h2 := Real.cosh_sq (π * u.im)
  ring_nf
  nlinarith [h1, h2]

/-- `|sin (π d)| ≥ 2 |d|` for `|d| ≤ 1/2`. -/
theorem two_mul_abs_le_abs_sin_pi_mul {d : ℝ} (hd : |d| ≤ 1 / 2) : 2 * |d| ≤ |Real.sin (π * d)| := by
  have h1 : Real.sin (π * |d|) = |Real.sin (π * d)| := by
    rcases le_or_gt 0 d with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos, abs_of_nonneg h])
    · rw [abs_of_neg h] at hd
      have hneg : Real.sin (π * d) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      rw [abs_of_neg h, mul_neg, Real.sin_neg, abs_of_neg hneg]
  rw [← h1]
  have := Real.mul_le_sin (x := π * |d|) (by positivity) (by nlinarith [Real.pi_pos])
  have hpi : 0 < π := Real.pi_pos
  calc 2 * |d| = 2 / π * (π * |d|) := by field_simp
    _ ≤ Real.sin (π * |d|) := this

/-- `|sinh t| ≥ |t|`. -/
theorem abs_le_abs_sinh (t : ℝ) : |t| ≤ |Real.sinh t| := by
  rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.2 (abs_nonneg t)

/-- Near an integer `m` with `|Re u - m| ≤ 1/2`, `|sin (π u)| ≥ 2 |u - m|`. -/
theorem two_mul_norm_sub_le_norm_sin_pi_mul (u : ℂ) (m : ℤ) (hm : |u.re - m| ≤ 1 / 2) :
    2 * ‖u - m‖ ≤ ‖Complex.sin (π * u)‖ := by
  have hsq := norm_sin_pi_mul_sq u
  have hsin : Real.sin (π * u.re) ^ 2 = Real.sin (π * (u.re - m)) ^ 2 := by
    rw [show π * u.re = π * (u.re - m) + m * π by ring, Real.sin_add_int_mul_pi, mul_pow,
      ← zpow_natCast, ← zpow_mul, Even.neg_one_zpow ⟨m, by ring⟩, one_mul]
  have hd := two_mul_abs_le_abs_sin_pi_mul hm
  have hy := abs_le_abs_sinh (π * u.im)
  have hpi : 2 ≤ π := by linarith [Real.pi_gt_three]
  have hsub : ‖u - m‖ ^ 2 = (u.re - m) ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : (2 * ‖u - m‖) ^ 2 ≤ ‖Complex.sin (π * u)‖ ^ 2 := by
    rw [hsq, hsin, mul_pow, hsub]
    have a1 : 4 * (u.re - m) ^ 2 ≤ Real.sin (π * (u.re - m)) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hd 2
      rw [mul_pow, sq_abs, sq_abs] at h; linarith
    have a2 : (π * u.im) ^ 2 ≤ Real.sinh (π * u.im) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hy 2
      rwa [sq_abs, sq_abs] at h
    have a3 : 4 * u.im ^ 2 ≤ (π * u.im) ^ 2 := by
      rw [mul_pow]
      nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ π ^ 2 - 4) (sq_nonneg u.im)]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h2


/-! ### `sin (π u) / u` -/

/-- `sincPi u = sin (π u) / u`, with the removable singularity at `0` filled in by `π`. -/
@[expose] noncomputable def sincPi : ℂ → ℂ := dslope (fun u => Complex.sin (π * u)) 0

theorem sincPi_of_ne {u : ℂ} (hu : u ≠ 0) : sincPi u = Complex.sin (π * u) / u := by
  rw [sincPi, dslope_of_ne _ hu, slope_def_field]; simp

theorem sincPi_zero : sincPi 0 = π := by
  rw [sincPi, dslope_same]
  have : HasDerivAt (fun u : ℂ => Complex.sin (π * u)) (Complex.cos (π * 0) * π) 0 := by
    have h := (Complex.hasDerivAt_sin (π * 0)).comp 0 ((hasDerivAt_id 0).const_mul (π : ℂ))
    exact h.congr_deriv (by simp)
  rw [this.deriv]; simp

theorem differentiable_sincPi : Differentiable ℂ sincPi := by
  rw [← differentiableOn_univ, sincPi, differentiableOn_dslope Filter.univ_mem]
  exact Differentiable.differentiableOn (by fun_prop)

theorem two_le_norm_sincPi {u : ℂ} (hu : |u.re| ≤ 1 / 2) : 2 ≤ ‖sincPi u‖ := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [sincPi_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  · rw [sincPi_of_ne hu0, norm_div, le_div_iff₀ (norm_pos_iff.2 hu0)]
    have := two_mul_norm_sub_le_norm_sin_pi_mul u 0 (by simpa using hu)
    simpa using this

theorem sincPi_ne_zero_of_ne_int {u : ℂ} (hu : ∀ n : ℤ, n ≠ 0 → u ≠ n) : sincPi u ≠ 0 := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [sincPi_zero]; exact_mod_cast Real.pi_ne_zero
  · rw [sincPi_of_ne hu0]
    refine div_ne_zero ?_ hu0
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hk' : u = k := by
      have := mul_left_cancel₀ hpi (hk.trans (mul_comm _ _))
      exact this
    rcases eq_or_ne k 0 with rfl | hk0
    · exact hu0 (by simpa using hk')
    · exact hu k hk0 hk'

/-! ### The Mordell integrand -/

theorem exp_sub_exp_neg_eq_two_I_sin (u : ℂ) :
    cexp (π * I * u) - cexp (-(π * I * u)) = 2 * I * Complex.sin (π * u) := by
  unfold Complex.sin
  have e1 : -(π * u) * I = -(π * I * u) := by ring
  have e2 : π * u * I = π * I * u := by ring
  rw [e1, e2]
  linear_combination (cexp (π * I * u) - cexp (-(π * I * u))) * Complex.I_sq

/-- The quadratic exponent `π i τ u² + 2 π i u z` of the Mordell integrand. -/
@[expose] noncomputable def mordellExponent (τ z u : ℂ) : ℂ := π * I * τ * u ^ 2 + 2 * π * I * u * z

/-- The Mordell integrand `exp (π i τ u² + 2 π i u z) / (exp (π i u) - exp (-π i u))`. -/
@[expose] noncomputable def mordellIntegrand (τ z u : ℂ) : ℂ :=
  cexp (mordellExponent τ z u) / (cexp (π * I * u) - cexp (-(π * I * u)))

/-- The constant in the Gaussian bound for the Mordell exponent along lines of direction `ω`
through points of norm at most `R`. -/
@[expose] noncomputable def mordellBoundConst (τ z : ℂ) (R : ℝ) : ℝ :=
  (2 * π * ‖τ‖ * R + 2 * π * ‖z‖) ^ 2 / (2 * π * τ.re) + π * ‖τ‖ * R ^ 2 + 2 * π * R * ‖z‖

theorem re_mordellExponent_le {τ z w : ℂ} (hτ : 0 < τ.re) {R : ℝ} (hw : ‖w‖ ≤ R) (x : ℝ) :
    (mordellExponent τ z (w - ω * x)).re ≤
      -(π * τ.re / 2) * x ^ 2 + mordellBoundConst τ z R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  have hsplit : mordellExponent τ z (w - ω * x) = (π * I * τ * ω ^ 2) * x ^ 2 +
      (-(2 * π * I * τ * ω * w) - 2 * π * I * ω * z) * x + (π * I * τ * w ^ 2 + 2 * π * I * w * z) := by
    unfold mordellExponent; ring
  rw [hsplit, add_re, add_re]
  -- the three pieces
  have h1 : (π * I * τ * ω ^ 2 * x ^ 2).re = -(π * τ.re * x ^ 2) := by
    rw [rsOmega_sq]
    have : (π : ℂ) * I * τ * I * x ^ 2 = ((-(π * x ^ 2) : ℝ) : ℂ) * τ := by
      push_cast; linear_combination (π * τ * x ^ 2) * Complex.I_sq
    rw [this, Complex.re_ofReal_mul]; ring
  set b : ℝ := 2 * π * ‖τ‖ * R + 2 * π * ‖z‖ with hb
  have hb0 : 0 ≤ b := by positivity
  have h2 : ((-(2 * π * I * τ * ω * w) - 2 * π * I * ω * z) * x).re ≤ b * |x| := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, norm_rsOmega, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, mul_one, Complex.norm_ofNat]
    rw [hb]; gcongr
  have h3 : (π * I * τ * w ^ 2 + 2 * π * I * w * z).re ≤ π * ‖τ‖ * R ^ 2 + 2 * π * R * ‖z‖ := by
    refine (Complex.re_le_norm _).trans ?_
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, norm_pow, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, mul_one, Complex.norm_ofNat]
    gcongr
  -- AM-GM
  set a : ℝ := π * τ.re / 2 with ha
  have ha0 : 0 < a := by positivity
  have hamgm : b * |x| ≤ a * x ^ 2 + b ^ 2 / (4 * a) := by
    have h4 : 0 ≤ (2 * a * |x| - b) ^ 2 := sq_nonneg _
    have h6 : a ^ 2 * |x| ^ 2 = a ^ 2 * x ^ 2 := by rw [sq_abs]
    have : b * |x| * (4 * a) ≤ (a * x ^ 2) * (4 * a) + b ^ 2 := by nlinarith
    calc b * |x| = b * |x| * (4 * a) / (4 * a) := by field_simp
      _ ≤ ((a * x ^ 2) * (4 * a) + b ^ 2) / (4 * a) := by gcongr
      _ = a * x ^ 2 + b ^ 2 / (4 * a) := by field_simp
  have hK : mordellBoundConst τ z R = b ^ 2 / (4 * a) + (π * ‖τ‖ * R ^ 2 + 2 * π * R * ‖z‖) := by
    rw [mordellBoundConst, hb, ha]; field_simp; ring
  rw [hK, h1]
  nlinarith

theorem two_mul_norm_sub_round_le_norm_sin_pi_mul (u : ℂ) :
    2 * ‖u - (round u.re : ℂ)‖ ≤ ‖Complex.sin (π * u)‖ :=
  two_mul_norm_sub_le_norm_sin_pi_mul u _ (abs_sub_round u.re)

/-- `mordellS u = u / (exp (π i u) - exp (-π i u))`, with its removable singularity at `0`
filled in. -/
@[expose] noncomputable def mordellS (u : ℂ) : ℂ := 1 / (2 * I * sincPi u)

theorem mordellS_zero : mordellS 0 = 1 / (2 * π * I) := by
  rw [mordellS, sincPi_zero]; ring

theorem norm_mordellS_le {u : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ n : ℤ, n ≠ 0 → ρ ≤ ‖u - n‖) : ‖mordellS u‖ ≤ 1 / 4 + ‖u‖ / (4 * ρ) := by
  rw [mordellS, norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  by_cases h : |u.re| ≤ 1 / 2
  · have := two_le_norm_sincPi h
    calc 1 / (2 * ‖sincPi u‖) ≤ 1 / (2 * 2) := by gcongr
      _ ≤ 1 / 4 + ‖u‖ / (4 * ρ) := by
        have : 0 ≤ ‖u‖ / (4 * ρ) := by positivity
        linarith
  · have hu0 : u ≠ 0 := by rintro rfl; simp at h
    have hr : round u.re ≠ 0 := by
      intro h0
      have := abs_sub_round u.re
      rw [h0] at this; simp at this; exact h (by rw [one_div]; exact this)
    have h1 := two_mul_norm_sub_round_le_norm_sin_pi_mul u
    have h2 := hu (round u.re) hr
    have h3 : 0 < ‖Complex.sin (π * u)‖ := by linarith
    rw [sincPi_of_ne hu0, norm_div]
    have e : 1 / (2 * (‖Complex.sin (π * u)‖ / ‖u‖)) = ‖u‖ / (2 * ‖Complex.sin (π * u)‖) := by
      field_simp
    rw [e]
    calc ‖u‖ / (2 * ‖Complex.sin (π * u)‖) ≤ ‖u‖ / (2 * (2 * ρ)) := by gcongr; linarith
      _ = ‖u‖ / (4 * ρ) := by ring
      _ ≤ 1 / 4 + ‖u‖ / (4 * ρ) := by linarith

theorem differentiableAt_mordellS {u : ℂ} (hu : sincPi u ≠ 0) : DifferentiableAt ℂ mordellS u := by
  unfold mordellS
  exact (differentiableAt_const _).div ((differentiableAt_const _).mul differentiable_sincPi.differentiableAt) (mul_ne_zero (by simp) hu)

theorem mordellIntegrand_eq_mordellS {τ z u : ℂ} (hu : u ≠ 0) :
    mordellIntegrand τ z u = cexp (mordellExponent τ z u) * mordellS u / u := by
  rw [mordellIntegrand, exp_sub_exp_neg_eq_two_I_sin, mordellS, sincPi_of_ne hu]
  field_simp

/-- `(A + B |x|) exp (-a x²) ≤ (A + B + B / a) exp (-(a/2) x²)`. -/
theorem affine_mul_exp_neg_sq_le {a A B : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℝ) :
    (A + B * |x|) * Real.exp (-a * x ^ 2) ≤ (A + B + B / a) * Real.exp (-(a / 2) * x ^ 2) := by
  have h1 : A + B * |x| ≤ (A + B + B / a) * Real.exp (a / 2 * x ^ 2) := by
    have h2 : a / 2 * x ^ 2 + 1 ≤ Real.exp (a / 2 * x ^ 2) := Real.add_one_le_exp _
    have h3 : |x| ≤ (1 + x ^ 2) / 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
    have h4 : 0 ≤ B / a := by positivity
    have h5 : B / a * (a / 2 * x ^ 2) = B / 2 * x ^ 2 := by field_simp
    have h6 : 0 ≤ (A + B) * (a / 2 * x ^ 2) := by positivity
    have h7 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ A + B + B / a)
    have h8 := mul_le_mul_of_nonneg_left h3 hB
    nlinarith [h5, h6, h7, h8]
  calc (A + B * |x|) * Real.exp (-a * x ^ 2)
      ≤ (A + B + B / a) * Real.exp (a / 2 * x ^ 2) * Real.exp (-a * x ^ 2) := by
        gcongr
    _ = (A + B + B / a) * Real.exp (-(a / 2) * x ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-! ### Lines `c - ω x` -/

/-- On the line `u = c - ω x` through a real `c`, `‖u - n‖ ≥ |c - n| √2/2` for every real `n`. -/
theorem norm_line_sub_ge (c x n : ℝ) :
    |c - n| * (Real.sqrt 2 / 2) ≤ ‖((c : ℂ) - ω * x) - n‖ := by
  refine le_trans ?_ (norm_sub_ge_abs_im_mul_conj_rsOmega _ _)
  have e : (ω * (x : ℂ)) * (starRingEnd ℂ) ω = (x : ℂ) := by
    rw [mul_right_comm, mul_comm ω, conj_rsOmega_mul, one_mul]
  have : (((c : ℂ) - ω * x) * (starRingEnd ℂ) ω).im = -(c * (Real.sqrt 2 / 2)) := by
    rw [sub_mul, sub_im, Complex.im_ofReal_mul, conj_rsOmega_im, e, Complex.ofReal_im]; ring
  rw [this, show -(c * (Real.sqrt 2 / 2)) + n * (Real.sqrt 2 / 2) = (n - c) * (Real.sqrt 2 / 2) by
    ring, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2 / 2), abs_sub_comm]

theorem norm_mordellIntegrand_eq (τ z u : ℂ) :
    ‖mordellIntegrand τ z u‖ = Real.exp (mordellExponent τ z u).re / (2 * ‖Complex.sin (π * u)‖) := by
  rw [mordellIntegrand, exp_sub_exp_neg_eq_two_I_sin, norm_div, Complex.norm_exp, norm_mul,
    norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]

/-- The Gaussian bound for the Mordell integrand on the line through a real `c` at distance at
least `δ` from the integers. -/
theorem norm_mordellIntegrand_line_le {τ z : ℂ} (hτ : 0 < τ.re) {c δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ n : ℤ, δ ≤ |c - n|) (x : ℝ) :
    ‖mordellIntegrand τ z (c - ω * x)‖ ≤
      Real.exp (mordellBoundConst τ z |c|) / (2 * Real.sqrt 2 * δ) *
        Real.exp (-(π * τ.re / 2) * x ^ 2) := by
  rw [norm_mordellIntegrand_eq]
  have hsin : Real.sqrt 2 * δ ≤ ‖Complex.sin (π * ((c : ℂ) - ω * x))‖ := by
    refine le_trans ?_ (two_mul_norm_sub_round_le_norm_sin_pi_mul _)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (norm_line_sub_ge c x _) zero_le_two)
    have := hc (round ((c : ℂ) - ω * x).re)
    nlinarith [Real.sqrt_nonneg 2]
  have hexp := re_mordellExponent_le (z := z) hτ (w := (c : ℂ)) (R := |c|) (by simp) x
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  have h2 : 0 < Real.sqrt 2 * δ := by positivity
  calc Real.exp (mordellExponent τ z ((c : ℂ) - ω * x)).re / (2 * ‖Complex.sin (π * ((c : ℂ) - ω * x))‖)
      ≤ Real.exp (mordellExponent τ z ((c : ℂ) - ω * x)).re / (2 * (Real.sqrt 2 * δ)) := by
        gcongr
    _ ≤ Real.exp (mordellBoundConst τ z |c| + -(π * τ.re / 2) * x ^ 2) / (2 * Real.sqrt 2 * δ) := by
        rw [mul_assoc]; gcongr; rw [add_comm]; exact hexp

theorem dist_round_pos {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) : 0 < |c - round c| := by
  rw [abs_pos, sub_ne_zero]; exact hc _

/-- The denominator of the Mordell integrand does not vanish on a line through a non-integer
real point. -/
theorem mordell_denom_line_ne_zero {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) (x : ℝ) :
    cexp (π * I * ((c : ℂ) - ω * x)) - cexp (-(π * I * ((c : ℂ) - ω * x))) ≠ 0 := by
    rw [exp_sub_exp_neg_eq_two_I_sin]
    refine mul_ne_zero (by simp) ?_
    rw [← norm_pos_iff]
    have h1 := two_mul_norm_sub_round_le_norm_sin_pi_mul ((c : ℂ) - ω * x)
    have h2 := norm_line_sub_ge c x (round ((c : ℂ) - ω * x).re)
    push_cast at h2
    have h3 := dist_round_pos hc
    have h4 := round_le c (round ((c : ℂ) - ω * x).re)
    have h5 : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
    have h6 := mul_le_mul_of_nonneg_right h4 h5.le
    have h7 := mul_pos h3 h5
    linarith

theorem continuous_mordellIntegrand_line {τ z : ℂ} {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) :
    Continuous fun x : ℝ => mordellIntegrand τ z (c - ω * x) := by
  unfold mordellIntegrand mordellExponent
  exact Continuous.div (by fun_prop) (by fun_prop) (mordell_denom_line_ne_zero hc)

theorem integrable_mordellIntegrand_line {τ z : ℂ} (hτ : 0 < τ.re) {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) :
    Integrable fun x : ℝ => mordellIntegrand τ z (c - ω * x) :=
  integrable_of_norm_le_gaussian (by positivity) (continuous_mordellIntegrand_line hc)
    (norm_mordellIntegrand_line_le hτ (dist_round_pos hc) (fun n => round_le c n))

/-- The Mordell integral `∫ exp (π i τ u² + 2 π i u z) / (exp (π i u) - exp (-π i u)) du` along
the line through the real point `c` in the direction `-ω = exp (5 π i / 4)`. -/
@[expose] noncomputable def mordell (τ z : ℂ) (c : ℝ) : ℂ :=
  ∫ x : ℝ, -ω * mordellIntegrand τ z (c - ω * x)

theorem mordellIntegrand_add_one_sub {τ z u : ℂ}
    (hu : cexp (π * I * u) - cexp (-(π * I * u)) ≠ 0) :
    mordellIntegrand τ (z + 1) u - mordellIntegrand τ z u =
      cexp (mordellExponent τ (z + 1 / 2) u) := by
  unfold mordellIntegrand
  rw [div_sub_div_same, div_eq_iff hu]
  have e1 : mordellExponent τ (z + 1) u = mordellExponent τ z u + 2 * π * I * u := by
    unfold mordellExponent; ring
  have e2 : mordellExponent τ (z + 1 / 2) u = mordellExponent τ z u + π * I * u := by
    unfold mordellExponent; ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  have e3 : cexp (2 * π * I * u) = cexp (π * I * u) * cexp (π * I * u) := by
    rw [← Complex.exp_add]; ring_nf
  have e4 : cexp (π * I * u) * cexp (-(π * I * u)) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [e3]
  linear_combination (cexp (mordellExponent τ z u)) * e4

/-- The Gaussian integral `∫ exp (π i τ u² + 2 π i u w) du` along a Riemann–Siegel line. -/
theorem integral_exp_mordellExponent_line {τ : ℂ} (hτ : 0 < τ.re) (w : ℂ) (c : ℝ) :
    ∫ x : ℝ, -ω * cexp (mordellExponent τ w (c - ω * x)) =
      -ω * (1 / τ) ^ (1 / 2 : ℂ) * cexp (-(π * I * w ^ 2 / τ)) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hsplit : ∀ x : ℝ, mordellExponent τ w (c - ω * x) = (-(π * τ)) * (x : ℂ) ^ 2 +
      (-(2 * π * I * ω * (τ * c + w))) * x + (π * I * τ * c ^ 2 + 2 * π * I * c * w) := by
    intro x; unfold mordellExponent
    linear_combination (π * I * τ * x ^ 2) * rsOmega_sq + (π * τ * x ^ 2) * Complex.I_sq
  simp_rw [hsplit, integral_const_mul]
  rw [integral_cexp_quadratic (by simp [hτ, Real.pi_pos])]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (π : ℂ) / -(-(π * τ)) = 1 / τ := by field_simp
  have hc' : (-(2 * π * I * ω * (τ * c + w))) ^ 2 = -(4 * π ^ 2 * I * (τ * c + w) ^ 2) := by
    linear_combination (4 * π ^ 2 * ω ^ 2 * (τ * c + w) ^ 2) * Complex.I_sq +
      (-(4 * π ^ 2 * (τ * c + w) ^ 2)) * rsOmega_sq
  have hd : (π * I * τ * c ^ 2 + 2 * π * I * c * w) -
      (-(2 * π * I * ω * (τ * c + w))) ^ 2 / (4 * -(π * τ)) = -(π * I * w ^ 2 / τ) := by
    rw [hc']; field_simp; ring
  rw [hb, hd]; ring

/-- The first functional equation of the Mordell integral: shifting `z` by `1` adds a Gaussian
integral. -/
theorem mordell_add_one {τ z : ℂ} (hτ : 0 < τ.re) {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) :
    mordell τ (z + 1) c =
      mordell τ z c + -ω * (1 / τ) ^ (1 / 2 : ℂ) * cexp (-(π * I * (z + 1 / 2) ^ 2 / τ)) := by
  rw [← integral_exp_mordellExponent_line hτ (z + 1 / 2) c, ← sub_eq_iff_eq_add',
    mordell, mordell, ← integral_sub ((integrable_mordellIntegrand_line hτ hc).const_mul _)
    ((integrable_mordellIntegrand_line hτ hc).const_mul _)]
  congr 1; ext x
  rw [← mul_sub, mordellIntegrand_add_one_sub (mordell_denom_line_ne_zero hc x)]

/-! ### The second functional equation -/

/-- On the strip between the lines through `c` and `c - 1`, the point `u = c - ω ξ` stays at
distance at least `min c (1 - c) √2/2` from every nonzero integer. -/
theorem norm_strip_sub_int_ge {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {ξ : ℂ}
    (hξ : ξ.im ∈ Icc (-(Real.sqrt 2 / 2)) 0) {n : ℤ} (hn : n ≠ 0) :
    min c (1 - c) * (Real.sqrt 2 / 2) ≤ ‖((c : ℂ) - ω * ξ) - n‖ := by
  refine le_trans ?_ (norm_sub_ge_abs_im_mul_conj_rsOmega _ _)
  have e : (ω * ξ) * (starRingEnd ℂ) ω = ξ := by
    rw [mul_right_comm, mul_comm ω, conj_rsOmega_mul, one_mul]
  have him : (((c : ℂ) - ω * ξ) * (starRingEnd ℂ) ω).im = -(c * (Real.sqrt 2 / 2)) - ξ.im := by
    rw [sub_mul, sub_im, Complex.im_ofReal_mul, conj_rsOmega_im, e]; ring
  rw [him]
  have hs : 0 < Real.sqrt 2 / 2 := by positivity
  obtain ⟨h1, h2⟩ := hξ
  rcases lt_or_gt_of_ne hn with h | h
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr h
    refine le_trans ((mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le).trans ?_) (neg_le_abs _)
    nlinarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast h
    refine le_trans ((mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le).trans ?_) (le_abs_self _)
    nlinarith

theorem neg_rsOmega_mul_mordellIntegrand_eq {τ z : ℂ} {c : ℝ} {ξ : ℂ}
    (hξ : ξ ≠ c * (starRingEnd ℂ) ω) :
    -ω * mordellIntegrand τ z (c - ω * ξ) =
      cexp (mordellExponent τ z (c - ω * ξ)) * mordellS (c - ω * ξ) /
        (ξ - c * (starRingEnd ℂ) ω) := by
  have hωc : ω * (c * (starRingEnd ℂ) ω) = c := by
    rw [mul_left_comm, mul_comm ω, conj_rsOmega_mul, mul_one]
  have hu : (c : ℂ) - ω * ξ = -ω * (ξ - c * (starRingEnd ℂ) ω) := by
    rw [neg_mul, mul_sub, hωc]; ring
  have hu0 : (c : ℂ) - ω * ξ ≠ 0 := by
    rw [hu]; exact mul_ne_zero (neg_ne_zero.2 rsOmega_ne_zero) (sub_ne_zero.2 hξ)
  rw [mordellIntegrand_eq_mordellS hu0, eq_div_iff (sub_ne_zero.2 hξ)]
  have hne := sub_ne_zero.2 hξ
  have hω := rsOmega_ne_zero
  calc -ω * (cexp (mordellExponent τ z (c - ω * ξ)) * mordellS (c - ω * ξ) / (c - ω * ξ)) *
        (ξ - c * (starRingEnd ℂ) ω)
      = cexp (mordellExponent τ z (c - ω * ξ)) * mordellS (c - ω * ξ) *
          ((-ω * (ξ - c * (starRingEnd ℂ) ω)) / (c - ω * ξ)) := by ring
    _ = cexp (mordellExponent τ z (c - ω * ξ)) * mordellS (c - ω * ξ) := by
        rw [← hu, div_self hu0, mul_one]


/-- The second functional equation of the Mordell integral: moving the line of integration from
`c` to `c - 1` (for `0 < c < 1`) crosses the pole at `u = 0` and changes the value by `-1`. -/
theorem mordell_eq_mordell_sub_one_sub_one {τ z : ℂ} (hτ : 0 < τ.re) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) : mordell τ z c = mordell τ z (c - 1) - 1 := by
  set β : ℝ := -(Real.sqrt 2 / 2) with hβ
  set N : ℂ → ℂ := fun ξ => cexp (mordellExponent τ z (c - ω * ξ)) * mordellS (c - ω * ξ) with hN
  set p : ℂ := c * (starRingEnd ℂ) ω with hp
  have hs : 0 < Real.sqrt 2 / 2 := by positivity
  have hs1 : Real.sqrt 2 / 2 < 1 := by
    have := Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (2 : ℝ) < 4)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    linarith
  have hpim : p.im = -(c * (Real.sqrt 2 / 2)) := by
    rw [hp, Complex.im_ofReal_mul, conj_rsOmega_im]; ring
  have hωc : ω * p = c := by
    rw [hp, mul_left_comm, mul_comm ω, conj_rsOmega_mul, mul_one]
  set ρ : ℝ := min c (1 - c) * (Real.sqrt 2 / 2) with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; have := lt_min hc0 (sub_pos.2 hc1); positivity
  set a₀ : ℝ := π * τ.re / 2 with ha₀
  have ha₀pos : 0 < a₀ := by positivity
  set K := mordellBoundConst τ z 2 with hK
  set A : ℝ := 1 / 4 + 2 / (4 * ρ) with hA
  set B : ℝ := 1 / (4 * ρ) with hB
  set C : ℝ := (A + B + B / a₀) * Real.exp K with hC
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  -- differentiability on the strip
  have hdist : ∀ ξ : ℂ, ξ.im ∈ Icc β 0 → ∀ n : ℤ, n ≠ 0 → ρ ≤ ‖((c : ℂ) - ω * ξ) - n‖ :=
    fun ξ hξ n hn => norm_strip_sub_int_ge hc0 hc1 hξ hn
  have hne : ∀ ξ : ℂ, ξ.im ∈ Icc β 0 → ∀ n : ℤ, n ≠ 0 → (c : ℂ) - ω * ξ ≠ n := by
    intro ξ hξ n hn h
    have := hdist ξ hξ n hn
    rw [h, sub_self, norm_zero] at this
    linarith
  have hdiff : ∀ ξ : ℂ, ξ.im ∈ Icc β 0 → DifferentiableAt ℂ N ξ := by
    intro ξ hξ
    refine DifferentiableAt.mul ?_ ?_
    · unfold mordellExponent; fun_prop
    · have hg : DifferentiableAt ℂ (fun ξ : ℂ => (c : ℂ) - ω * ξ) ξ := by fun_prop
      have := DifferentiableAt.comp (g := mordellS) (f := fun ξ : ℂ => (c : ℂ) - ω * ξ) ξ
        (differentiableAt_mordellS (sincPi_ne_zero_of_ne_int (hne ξ hξ))) hg
      exact this
  -- Gaussian bound on the strip
  have hbound : ∀ ξ : ℂ, ξ.im ∈ Icc β 0 → ‖N ξ‖ ≤ C * Real.exp (-(a₀ / 2) * ξ.re ^ 2) := by
    intro ξ hξ
    set w : ℂ := c - ω * (ξ.im * I) with hw
    have hu : (c : ℂ) - ω * ξ = w - ω * ξ.re := by
      have : ω * ξ = ω * ξ.re + ω * (ξ.im * I) := by rw [← mul_add, Complex.re_add_im]
      rw [this, hw]; ring
    have hw2 : ‖w‖ ≤ 2 := by
      rw [hw]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_rsOmega, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc0, one_mul, mul_one]
      obtain ⟨h1, h2⟩ := hξ
      have : |ξ.im| ≤ Real.sqrt 2 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
      linarith
    have hQ := re_mordellExponent_le (z := z) hτ hw2 ξ.re
    rw [← hu] at hQ
    have hS := norm_mordellS_le hρ0 (hdist ξ hξ)
    have hunorm : ‖(c : ℂ) - ω * ξ‖ ≤ 2 + |ξ.re| := by
      rw [hu]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_rsOmega, one_mul, Complex.norm_real, Real.norm_eq_abs]
      linarith
    have hS' : ‖mordellS ((c : ℂ) - ω * ξ)‖ ≤ A + B * |ξ.re| := by
      refine hS.trans ?_
      rw [hA, hB]
      have : ‖(c : ℂ) - ω * ξ‖ / (4 * ρ) ≤ (2 + |ξ.re|) / (4 * ρ) := by gcongr
      calc 1 / 4 + ‖(c : ℂ) - ω * ξ‖ / (4 * ρ) ≤ 1 / 4 + (2 + |ξ.re|) / (4 * ρ) := by linarith
        _ = 1 / 4 + 2 / (4 * ρ) + 1 / (4 * ρ) * |ξ.re| := by ring
    calc ‖N ξ‖ = Real.exp (mordellExponent τ z ((c : ℂ) - ω * ξ)).re *
          ‖mordellS ((c : ℂ) - ω * ξ)‖ := by
          show ‖cexp (mordellExponent τ z ((c : ℂ) - ω * ξ)) * mordellS ((c : ℂ) - ω * ξ)‖ = _
          rw [norm_mul, Complex.norm_exp]
      _ ≤ Real.exp (-a₀ * ξ.re ^ 2 + K) * (A + B * |ξ.re|) :=
          mul_le_mul (Real.exp_le_exp.2 (by rw [ha₀, hK]; linarith)) hS' (norm_nonneg _)
            (Real.exp_pos _).le
      _ = (A + B * |ξ.re|) * Real.exp (-a₀ * ξ.re ^ 2) * Real.exp K := by
          rw [Real.exp_add]; ring
      _ ≤ (A + B + B / a₀) * Real.exp (-(a₀ / 2) * ξ.re ^ 2) * Real.exp K :=
          mul_le_mul_of_nonneg_right (affine_mul_exp_neg_sq_le ha₀pos hA0 hB0 ξ.re)
            (Real.exp_pos K).le
      _ = C * Real.exp (-(a₀ / 2) * ξ.re ^ 2) := by rw [hC]; ring
  -- the residue theorem
  have key := integral_div_sub_add_ofReal_mul_I_sub_integral_div_sub_of_neg (N := N) (p := p)
    (β := β) (a := a₀ / 2) (C := C) (by positivity)
    (by rw [hpim, hβ]; nlinarith [mul_pos (sub_pos.2 hc1) hs]) (by rw [hpim]; nlinarith) hdiff hbound
  have hNp : N p = 1 / (2 * π * I) := by
    rw [hN]; simp only []
    rw [show (c : ℂ) - ω * p = 0 by rw [hωc, sub_self], mordellS_zero]
    simp [mordellExponent]
  have h1 : (∫ x : ℝ, N x / (x - p)) = mordell τ z c := by
    rw [mordell]; congr 1; ext x
    rw [neg_rsOmega_mul_mordellIntegrand_eq]
    intro h
    have := congrArg Complex.im h
    rw [Complex.ofReal_im, ← hp, hpim] at this
    nlinarith
  have hγ : ((Real.sqrt 2 : ℝ) : ℂ) / 2 + β * I = (starRingEnd ℂ) ω := by
    apply Complex.ext <;> simp [rsOmega_re, rsOmega_im, hβ]
  have h2 : (∫ x : ℝ, N (x + β * I) / (x + β * I - p)) = mordell τ z (c - 1) := by
    rw [mordell]
    have e : ∀ x : ℝ, ((c - 1 : ℝ) : ℂ) - ω * x =
        c - ω * (((x + Real.sqrt 2 / 2 : ℝ) : ℂ) + β * I) := by
      intro x; push_cast
      have := conj_rsOmega_mul
      rw [add_assoc, hγ, mul_add]; linear_combination this
    simp_rw [e]
    rw [← integral_add_right_eq_self (fun x : ℝ => N (x + β * I) / (x + β * I - p))
      (Real.sqrt 2 / 2)]
    congr 1; ext x
    rw [neg_rsOmega_mul_mordellIntegrand_eq]
    intro h
    have := congrArg Complex.im h
    rw [← hp, hpim] at this
    simp [hβ] at this
    nlinarith
  rw [h1, h2, hNp] at key
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : 2 * (π : ℂ) * I * (1 / (2 * π * I)) = 1 := by field_simp
  rw [this] at key
  linear_combination -key

end Complex
