/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.Analysis.Complex.RiemannSiegelLine
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Riemann–Siegel integral

This file defines the Riemann–Siegel integral
`R(s, c) = ∫_{c ↙} u^{-s} e^{iπu²} / (e^{iπu} - e^{-iπu}) du`
along the Riemann–Siegel line `u = c - ω x` (`x : ℝ`, `ω = exp (π i / 4)`) through a positive
non-integer real point `c`, and establishes its basic properties:

* `RiemannSiegel.norm_integrand_le`: a Gaussian bound `‖u^{-s} e^{iπu²} / (e^{iπu} - e^{-iπu})‖ ≤
  K exp (-π (Im u)²)` on the closed strip `c ≤ Re u - Im u ≤ c'`, uniform in `s` on bounded sets;
* `RiemannSiegel.integrable_integrand_line`: integrability along the lines;
* `RiemannSiegel.differentiable_rsIntegral`: `s ↦ R(s, c)` is entire;
* `RiemannSiegel.rsIntegral_add_one`: moving the line from `c ∈ (n - 1, n)` to `c' ∈ (n, n + 1)`
  across the pole at `u = n` subtracts `n^{-s}`, so that
  `R(s, N + 1/2) = R(s, 1/2) - ∑_{n=1}^N n^{-s}` (`rsIntegral_add_half`).

The value `R(s, 1/2)` is the function `R_{0,0}(s)` of the Riemann–Siegel formula
`ζ(s) = R(s) + χ(s) conj (R (conj (1 - s)))` (Polymath (5.3) and Titchmarsh (2.10.6)), proved in
`LemmaLib.NumberTheory.RiemannSiegel.Formula`.
-/

public section

open Complex Real Set Filter Topology MeasureTheory

local notation "ω" => Complex.rsOmega

namespace RiemannSiegel

/-- The Riemann–Siegel kernel `e^{iπu²} / (e^{iπu} - e^{-iπu})`. -/
@[expose] noncomputable def kernel (u : ℂ) : ℂ :=
  cexp (π * I * u ^ 2) / (cexp (π * I * u) - cexp (-(π * I * u)))

theorem kernel_eq_mordellIntegrand (u : ℂ) : kernel u = mordellIntegrand 1 0 u := by
  unfold kernel mordellIntegrand mordellExponent; simp

/-- The Riemann–Siegel integrand `u^{-s} e^{iπu²} / (e^{iπu} - e^{-iπu})`. -/
@[expose] noncomputable def integrand (s u : ℂ) : ℂ := u ^ (-s) * kernel u

/-- The Riemann–Siegel integral `∫_{c ↙} u^{-s} e^{iπu²} / (e^{iπu} - e^{-iπu}) du` along the
line `u = c - ω x` through the real point `c`. -/
@[expose] noncomputable def rsIntegral (s : ℂ) (c : ℝ) : ℂ :=
  ∫ x : ℝ, -ω * integrand s (c - ω * x)

/-! ### Elementary bounds -/

theorem abs_re_sub_im_le_sqrt_two_mul_norm (u : ℂ) : |u.re - u.im| ≤ Real.sqrt 2 * ‖u‖ := by
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul (by norm_num)]
  apply Real.abs_le_sqrt
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (u.re + u.im)]

theorem norm_le_abs_re_sub_im_add (u : ℂ) : ‖u‖ ≤ |u.re - u.im| + 2 * |u.im| := by
  refine (Complex.norm_le_abs_re_add_abs_im u).trans ?_
  have := abs_sub_abs_le_abs_sub u.re u.im
  linarith [abs_sub (u.re) (u.im)]

theorem norm_cpow_neg_le {u : ℂ} (hu : u ≠ 0) (s : ℂ) :
    ‖u ^ (-s)‖ ≤ ‖u‖ ^ (-s.re) * Real.exp (π * |s.im|) := by
  rw [Complex.norm_cpow_of_ne_zero hu, neg_re, neg_im, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  calc -(arg u * -s.im) = arg u * s.im := by ring
    _ ≤ |arg u * s.im| := le_abs_self _
    _ = |arg u| * |s.im| := abs_mul _ _
    _ ≤ π * |s.im| := by gcongr; exact Complex.abs_arg_le_pi u

theorem abs_log_le_add_inv {y : ℝ} (hy : 0 < y) : |Real.log y| ≤ y + 1 / y := by
  have h1 : 0 < 1 / y := by positivity
  rcases le_or_gt 1 y with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    linarith [Real.log_le_sub_one_of_pos hy]
  · rw [abs_of_neg (Real.log_neg hy h), ← Real.log_inv, ← one_div]
    linarith [Real.log_le_sub_one_of_pos h1]

theorem rpow_neg_le_exp {y σ : ℝ} (hy : 0 < y) : y ^ (-σ) ≤ Real.exp (|σ| * (y + 1 / y)) := by
  rw [Real.rpow_def_of_pos hy]
  apply Real.exp_le_exp.2
  calc Real.log y * -σ ≤ |Real.log y * -σ| := le_abs_self _
    _ = |Real.log y| * |σ| := by rw [abs_mul, abs_neg]
    _ ≤ (y + 1 / y) * |σ| := by gcongr; exact abs_log_le_add_inv hy
    _ = |σ| * (y + 1 / y) := by ring

theorem norm_exp_pi_I_mul_sq (u : ℂ) :
    ‖cexp (π * I * u ^ 2)‖ = Real.exp (-(2 * π) * u.re * u.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, sq, zero_mul, mul_zero,
    mul_one, sub_self, add_zero, zero_sub]
  ring

/-- A linear-times-Gaussian bound: `M |y| - 2 π y² ≤ M² / (4π) - π y²`. -/
theorem mul_abs_sub_le (M y : ℝ) : M * |y| - 2 * π * y ^ 2 ≤ M ^ 2 / (4 * π) - π * y ^ 2 := by
  have hπ := Real.pi_pos
  have h := sq_nonneg (2 * π * |y| - M)
  have hy : |y| ^ 2 = y ^ 2 := sq_abs y
  rw [sub_le_sub_iff, ← sub_nonneg]
  have : M ^ 2 / (4 * π) - M * |y| + π * y ^ 2 = (2 * π * |y| - M) ^ 2 / (4 * π) := by
    field_simp; rw [← hy]; ring
  nlinarith [div_nonneg h (by positivity : (0 : ℝ) ≤ 4 * π)]

/-! ### The Gaussian bound on strips -/

/-- The constant of the Gaussian bound `norm_integrand_le` on the strip `c ≤ Re u - Im u ≤ c'`,
for `|Re s| ≤ σ₀`, `|Im s| ≤ θ₀` and lines at distance `≥ ρ` from the integers. -/
@[expose] noncomputable def boundConst (σ₀ θ₀ c c' ρ : ℝ) : ℝ :=
  Real.sqrt 2 / (4 * ρ) *
    Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) + (2 * σ₀ + 2 * π * c') ^ 2 / (4 * π))

theorem boundConst_nonneg {σ₀ θ₀ c c' ρ : ℝ} (hρ : 0 < ρ) : 0 ≤ boundConst σ₀ θ₀ c c' ρ := by
  unfold boundConst; positivity

theorem boundConst_mono {σ₀ θ₀ c c' ρ σ₀' θ₀' : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hcc' : c ≤ c')
    (hσ₀0 : 0 ≤ σ₀) (hσ₀ : σ₀ ≤ σ₀') (hθ₀ : θ₀ ≤ θ₀') :
    boundConst σ₀ θ₀ c c' ρ ≤ boundConst σ₀' θ₀' c c' ρ := by
  unfold boundConst
  have hπ := Real.pi_pos
  have hc' : 0 < c' := hc.trans_le hcc'
  have hX : 0 ≤ c' + Real.sqrt 2 / c := by positivity
  have h1 : 0 ≤ 2 * σ₀ + 2 * π * c' := by positivity
  have h2 : 2 * σ₀ + 2 * π * c' ≤ 2 * σ₀' + 2 * π * c' := by linarith
  have h3 : (2 * σ₀ + 2 * π * c') ^ 2 ≤ (2 * σ₀' + 2 * π * c') ^ 2 := by gcongr
  have h4 : σ₀ * (c' + Real.sqrt 2 / c) ≤ σ₀' * (c' + Real.sqrt 2 / c) := by gcongr
  have h5 : (2 * σ₀ + 2 * π * c') ^ 2 / (4 * π) ≤ (2 * σ₀' + 2 * π * c') ^ 2 / (4 * π) := by
    gcongr
  gcongr

/-- The point `u` lies in `slitPlane` when `0 < Re u - Im u`. -/
theorem mem_slitPlane_of_re_sub_im_pos {u : ℂ} (hu : 0 < u.re - u.im) : u ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases h : u.im = 0
  · left; rw [h, sub_zero] at hu; exact hu
  · right; exact h

theorem ne_zero_of_re_sub_im_pos {u : ℂ} (hu : 0 < u.re - u.im) : u ≠ 0 := by
  intro h; rw [h] at hu; simp at hu

/-- The Riemann–Siegel kernel is bounded by `√2 / (4 ρ)` on a strip whose lines stay at
distance `≥ ρ` from the integers. -/
theorem norm_kernel_le {u : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hu : ∀ m : ℤ, ρ ≤ |u.re - u.im - m|) :
    ‖kernel u‖ ≤ Real.sqrt 2 / (4 * ρ) * Real.exp (-(2 * π) * u.re * u.im) := by
  unfold kernel
  rw [exp_sub_exp_neg_eq_two_I_sin, norm_div, norm_exp_pi_I_mul_sq, norm_mul, norm_mul,
    Complex.norm_two, Complex.norm_I, mul_one]
  set m : ℤ := round u.re with hm
  have hre : |u.re - m| ≤ 1 / 2 := by rw [hm]; exact abs_sub_round u.re
  have h1 := two_mul_norm_sub_le_norm_sin_pi_mul u m hre
  have h2 : ρ ≤ Real.sqrt 2 * ‖u - m‖ := by
    refine (hu m).trans ?_
    have := abs_re_sub_im_le_sqrt_two_mul_norm (u - m)
    rwa [sub_re, sub_im, Complex.intCast_re, Complex.intCast_im, sub_zero, sub_right_comm]
      at this
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsin : 0 < ‖Complex.sin (π * u)‖ := by
    have : 0 < ‖u - m‖ := by nlinarith
    linarith
  rw [div_le_iff₀ (by positivity)]
  have hE := Real.exp_pos (-(2 * π) * u.re * u.im)
  have h3 : 1 ≤ Real.sqrt 2 / (4 * ρ) * (2 * ‖Complex.sin (π * u)‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc Real.exp (-(2 * π) * u.re * u.im) = Real.exp (-(2 * π) * u.re * u.im) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-(2 * π) * u.re * u.im) *
        (Real.sqrt 2 / (4 * ρ) * (2 * ‖Complex.sin (π * u)‖)) := by gcongr
    _ = _ := by ring

/-- The Gaussian bound on the strip `c ≤ Re u - Im u ≤ c'`:
`‖integrand s u‖ ≤ boundConst σ₀ θ₀ c c' ρ * exp (-π (Im u)²)` when `|Re s| ≤ σ₀`, `|Im s| ≤ θ₀`,
`0 < c` and every `κ ∈ [c, c']` is at distance `≥ ρ` from the integers. -/
theorem norm_integrand_le {s u : ℂ} {σ₀ θ₀ c c' ρ : ℝ} (hσ₀ : |s.re| ≤ σ₀) (hθ₀ : |s.im| ≤ θ₀)
    (hc : 0 < c) (hρ : 0 < ρ) (hstrip : ∀ κ ∈ Icc c c', ∀ m : ℤ, ρ ≤ |κ - m|)
    (hu : u.re - u.im ∈ Icc c c') :
    ‖integrand s u‖ ≤ boundConst σ₀ θ₀ c c' ρ * Real.exp (-π * u.im ^ 2) := by
  set κ := u.re - u.im with hκ
  set y := u.im with hy
  have hκc : c ≤ κ := hu.1
  have hκc' : κ ≤ c' := hu.2
  have hκ0 : 0 < κ := hc.trans_le hκc
  have hu0 : u ≠ 0 := ne_zero_of_re_sub_im_pos hκ0
  have hnorm0 : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hs2 : 0 < Real.sqrt 2 := by positivity
  -- bounds on `‖u‖`
  have hlow : κ ≤ Real.sqrt 2 * ‖u‖ := by
    have := abs_re_sub_im_le_sqrt_two_mul_norm u
    rwa [← hκ, abs_of_pos hκ0] at this
  have hinv : 1 / ‖u‖ ≤ Real.sqrt 2 / c := by
    rw [div_le_div_iff₀ hnorm0 hc]
    nlinarith
  have hup : ‖u‖ ≤ c' + 2 * |y| := by
    have := norm_le_abs_re_sub_im_add u
    rw [← hκ, abs_of_pos hκ0] at this
    linarith
  -- the power
  have hpow : ‖u ^ (-s)‖ ≤ Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) + 2 * σ₀ * |y|) := by
    refine (norm_cpow_neg_le hu0 s).trans ?_
    have hσ₀0 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ₀
    calc ‖u‖ ^ (-s.re) * Real.exp (π * |s.im|)
        ≤ Real.exp (|s.re| * (‖u‖ + 1 / ‖u‖)) * Real.exp (π * |s.im|) :=
          mul_le_mul_of_nonneg_right (rpow_neg_le_exp hnorm0) (Real.exp_pos _).le
      _ ≤ Real.exp (σ₀ * (c' + 2 * |y| + Real.sqrt 2 / c)) * Real.exp (π * θ₀) := by
          have h1 : |s.re| * (‖u‖ + 1 / ‖u‖) ≤ σ₀ * (c' + 2 * |y| + Real.sqrt 2 / c) := by
            have : 0 ≤ ‖u‖ + 1 / ‖u‖ := by positivity
            calc |s.re| * (‖u‖ + 1 / ‖u‖) ≤ σ₀ * (‖u‖ + 1 / ‖u‖) := by gcongr
              _ ≤ σ₀ * (c' + 2 * |y| + Real.sqrt 2 / c) := by gcongr
          have h2 : π * |s.im| ≤ π * θ₀ := by gcongr
          exact mul_le_mul (Real.exp_le_exp.2 h1) (Real.exp_le_exp.2 h2) (Real.exp_pos _).le
            (Real.exp_pos _).le
      _ = Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) + 2 * σ₀ * |y|) := by
          rw [← Real.exp_add]; congr 1; ring
  -- the kernel
  have hker := norm_kernel_le hρ (fun m => hstrip κ hu m)
  have hre : u.re = y + κ := by rw [hκ, hy]; ring
  have hgauss : -(2 * π) * u.re * u.im ≤ 2 * π * c' * |y| - 2 * π * y ^ 2 := by
    rw [hre]
    have : -(2 * π) * (y + κ) * y = -(2 * π) * κ * y - 2 * π * y ^ 2 := by ring
    rw [this]
    have h1 : -(2 * π) * κ * y ≤ 2 * π * c' * |y| := by
      have : -(2 * π) * κ * y ≤ |2 * π * κ * y| := by
        rw [show -(2 * π) * κ * y = -(2 * π * κ * y) by ring]; exact neg_le_abs _
      refine this.trans ?_
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π * κ)]
      gcongr
    linarith
  -- combine
  unfold integrand
  rw [norm_mul]
  have hσ₀0 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ₀
  have hker' : ‖kernel u‖ ≤ Real.sqrt 2 / (4 * ρ) * Real.exp (2 * π * c' * |y| - 2 * π * y ^ 2) := by
    refine hker.trans ?_
    gcongr
  calc ‖u ^ (-s)‖ * ‖kernel u‖
      ≤ Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) + 2 * σ₀ * |y|) *
          (Real.sqrt 2 / (4 * ρ) * Real.exp (2 * π * c' * |y| - 2 * π * y ^ 2)) := by
        gcongr
    _ = Real.sqrt 2 / (4 * ρ) * (Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) + 2 * σ₀ * |y|) *
          Real.exp (2 * π * c' * |y| - 2 * π * y ^ 2)) := by ring
    _ = Real.sqrt 2 / (4 * ρ) * Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) +
          ((2 * σ₀ + 2 * π * c') * |y| - 2 * π * y ^ 2)) := by
        rw [← Real.exp_add]; congr 2; ring
    _ ≤ Real.sqrt 2 / (4 * ρ) * Real.exp (π * θ₀ + σ₀ * (c' + Real.sqrt 2 / c) +
          ((2 * σ₀ + 2 * π * c') ^ 2 / (4 * π) - π * y ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        linarith [mul_abs_sub_le (2 * σ₀ + 2 * π * c') y]
    _ = boundConst σ₀ θ₀ c c' ρ * Real.exp (-π * u.im ^ 2) := by
        unfold boundConst
        rw [← hy, mul_assoc (Real.sqrt 2 / (4 * ρ)), ← Real.exp_add]
        congr 2; ring

/-! ### The lines `u = c - ω x` -/

theorem re_sub_im_line (c x : ℝ) : ((c : ℂ) - ω * x).re - ((c : ℂ) - ω * x).im = c := by
  rw [re_sub_im_sub_rsOmega_mul]; simp

theorem im_line (c x : ℝ) : ((c : ℂ) - ω * x).im = -(Real.sqrt 2 / 2) * x := by
  rw [im_sub_rsOmega_mul]; simp

theorem im_line_sq (c x : ℝ) : ((c : ℂ) - ω * x).im ^ 2 = x ^ 2 / 2 := by
  rw [im_line, mul_pow, neg_sq, sqrt_two_div_two_sq]; ring

theorem abs_im_line_le (c x : ℝ) : |((c : ℂ) - ω * x).im| ≤ |x| := by
  rw [im_line, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2 / 2)]
  have h1 : Real.sqrt 2 / 2 ≤ 1 := by
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have := abs_nonneg x
  nlinarith

theorem line_mem_slitPlane {c : ℝ} (hc0 : 0 < c) (x : ℝ) : (c : ℂ) - ω * x ∈ slitPlane :=
  mem_slitPlane_of_re_sub_im_pos (by rw [re_sub_im_line]; exact hc0)

theorem line_ne_zero {c : ℝ} (hc0 : 0 < c) (x : ℝ) : (c : ℂ) - ω * x ≠ 0 :=
  ne_zero_of_re_sub_im_pos (by rw [re_sub_im_line]; exact hc0)

theorem continuous_integrand_line (s : ℂ) {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) :
    Continuous fun x : ℝ => integrand s (c - ω * x) := by
  unfold integrand kernel
  refine Continuous.mul ?_
    (Continuous.div (by fun_prop) (by fun_prop) (mordell_denom_line_ne_zero hc))
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hf : ContinuousAt (fun x : ℝ => (c : ℂ) - ω * x) x := by fun_prop
  exact ContinuousAt.comp (g := fun u : ℂ => u ^ (-s))
    (continuousAt_cpow_const (line_mem_slitPlane hc0 x)) hf

theorem continuous_log_line {c : ℝ} (hc0 : 0 < c) :
    Continuous fun x : ℝ => Complex.log (c - ω * x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hf : ContinuousAt (fun x : ℝ => (c : ℂ) - ω * x) x := by fun_prop
  exact ContinuousAt.comp (g := Complex.log) (continuousAt_clog (line_mem_slitPlane hc0 x)) hf

theorem strip_dist_line (c : ℝ) : ∀ κ ∈ Icc c c, ∀ m : ℤ, |c - round c| ≤ |κ - m| := by
  intro κ hκ m
  rw [Icc_self, mem_singleton_iff] at hκ
  rw [hκ]; exact round_le c m

theorem norm_integrand_line_le {s : ℂ} {σ₀ θ₀ : ℝ} (hσ₀ : |s.re| ≤ σ₀) (hθ₀ : |s.im| ≤ θ₀)
    {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) (x : ℝ) :
    ‖integrand s (c - ω * x)‖ ≤
      boundConst σ₀ θ₀ c c |c - round c| * Real.exp (-(π / 2) * x ^ 2) := by
  have := norm_integrand_le hσ₀ hθ₀ hc0 (dist_round_pos hc) (strip_dist_line c)
    (u := c - ω * x) (by rw [re_sub_im_line]; exact ⟨le_rfl, le_rfl⟩)
  rwa [im_line_sq, show -π * (x ^ 2 / 2) = -(π / 2) * x ^ 2 by ring] at this

theorem integrable_integrand_line (s : ℂ) {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) :
    Integrable fun x : ℝ => integrand s (c - ω * x) :=
  integrable_of_norm_le_gaussian (by positivity) (continuous_integrand_line s hc0 hc)
    (norm_integrand_line_le le_rfl le_rfl hc0 hc)

/-! ### Differentiability in `s` -/

theorem norm_log_le_of_strip {u : ℂ} {c c' : ℝ} (hc : 0 < c) (hu : u.re - u.im ∈ Icc c c') :
    ‖Complex.log u‖ ≤ c' + Real.sqrt 2 / c + π + 2 * |u.im| := by
  have hκ0 : 0 < u.re - u.im := hc.trans_le hu.1
  have hu0 := ne_zero_of_re_sub_im_pos hκ0
  have hnorm0 : 0 < ‖u‖ := norm_pos_iff.2 hu0
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]
  have h1 := abs_log_le_add_inv hnorm0
  have h2 := Complex.abs_arg_le_pi u
  have hlow : u.re - u.im ≤ Real.sqrt 2 * ‖u‖ := by
    have := abs_re_sub_im_le_sqrt_two_mul_norm u
    rwa [abs_of_pos hκ0] at this
  have hinv : 1 / ‖u‖ ≤ Real.sqrt 2 / c := by
    rw [div_le_div_iff₀ hnorm0 hc]
    nlinarith [hu.1]
  have hup : ‖u‖ ≤ c' + 2 * |u.im| := by
    have := norm_le_abs_re_sub_im_add u
    rw [abs_of_pos hκ0] at this
    linarith [hu.2]
  linarith

theorem hasDerivAt_integrand {u : ℂ} (hu : u ≠ 0) (s : ℂ) :
    HasDerivAt (fun s => integrand s u) (-(Complex.log u * integrand s u)) s := by
  unfold integrand
  exact (((hasDerivAt_neg s).const_cpow (c := u) (Or.inl hu)).mul_const (kernel u)).congr_deriv
    (by ring)

theorem norm_log_mul_integrand_line_le {s : ℂ} {σ₀ θ₀ : ℝ} (hσ₀ : |s.re| ≤ σ₀)
    (hθ₀ : |s.im| ≤ θ₀) {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) (x : ℝ) :
    ‖Complex.log (c - ω * x) * integrand s (c - ω * x)‖ ≤
      (c + Real.sqrt 2 / c + π + 2 + 4 / π) * boundConst σ₀ θ₀ c c |c - round c| *
        Real.exp (-(π / 4) * x ^ 2) := by
  rw [norm_mul]
  have h1 := norm_log_le_of_strip hc0 (u := c - ω * x)
    (by rw [re_sub_im_line]; exact ⟨le_rfl, le_rfl⟩)
  have h2 := norm_integrand_line_le hσ₀ hθ₀ hc0 hc x
  have h3 := abs_im_line_le c x
  have hK := boundConst_nonneg (σ₀ := σ₀) (θ₀ := θ₀) (c := c) (c' := c) (dist_round_pos hc)
  set A : ℝ := c + Real.sqrt 2 / c + π with hA
  set K := boundConst σ₀ θ₀ c c |c - round c| with hK'
  have hA0 : 0 ≤ A := by positivity
  have hπ : 0 < π / 2 := by positivity
  calc ‖Complex.log (c - ω * x)‖ * ‖integrand s (c - ω * x)‖
      ≤ (A + 2 * |x|) * (K * Real.exp (-(π / 2) * x ^ 2)) :=
        mul_le_mul (h1.trans (show A + 2 * |((c : ℂ) - ω * x).im| ≤ A + 2 * |x| by linarith)) h2
          (norm_nonneg _) (by positivity : (0 : ℝ) ≤ A + 2 * |x|)
    _ = K * ((A + 2 * |x|) * Real.exp (-(π / 2) * x ^ 2)) := by ring
    _ ≤ K * ((A + 2 + 2 / (π / 2)) * Real.exp (-(π / 2 / 2) * x ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (affine_mul_exp_neg_sq_le (B := 2) hπ hA0 (by norm_num) x)
          hK
    _ = (A + 2 + 4 / π) * K * Real.exp (-(π / 4) * x ^ 2) := by
        rw [show π / 2 / 2 = π / 4 by ring, show 2 / (π / 2) = 4 / π by rw [div_div_eq_mul_div]; norm_num]
        ring

theorem abs_re_le_of_mem_ball {s s₀ : ℂ} (hs : s ∈ Metric.ball s₀ 1) :
    |s.re| ≤ |s₀.re| + 1 ∧ |s.im| ≤ |s₀.im| + 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have h1 := Complex.abs_re_le_norm (s - s₀)
  have h2 := Complex.abs_im_le_norm (s - s₀)
  rw [sub_re] at h1
  rw [sub_im] at h2
  constructor
  · calc |s.re| = |(s.re - s₀.re) + s₀.re| := by ring_nf
      _ ≤ |s.re - s₀.re| + |s₀.re| := abs_add_le _ _
      _ ≤ |s₀.re| + 1 := by linarith
  · calc |s.im| = |(s.im - s₀.im) + s₀.im| := by ring_nf
      _ ≤ |s.im - s₀.im| + |s₀.im| := abs_add_le _ _
      _ ≤ |s₀.im| + 1 := by linarith

/-- The Riemann–Siegel integral is differentiable in `s`, with derivative obtained by
differentiating under the integral sign. -/
theorem hasDerivAt_rsIntegral (s₀ : ℂ) {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) :
    HasDerivAt (fun s => rsIntegral s c)
      (∫ x : ℝ, -ω * -(Complex.log (c - ω * x) * integrand s₀ (c - ω * x))) s₀ := by
  unfold rsIntegral
  set σ₀ : ℝ := |s₀.re| + 1 with hσ₀
  set θ₀ : ℝ := |s₀.im| + 1 with hθ₀
  set K : ℝ := (c + Real.sqrt 2 / c + π + 2 + 4 / π) * boundConst σ₀ θ₀ c c |c - round c|
    with hK
  have hmeas : ∀ s : ℂ,
      AEStronglyMeasurable (fun x : ℝ => -ω * integrand s (c - ω * x)) volume :=
    fun s => (continuous_const.mul (continuous_integrand_line s hc0 hc)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall hmeas) ((integrable_integrand_line s₀ hc0 hc).const_mul _)
    (F' := fun s x => -ω * -(Complex.log (c - ω * x) * integrand s (c - ω * x)))
    ?_ (bound := fun x => K * Real.exp (-(π / 4) * x ^ 2)) ?_ ?_ ?_).2
  · exact (continuous_const.mul ((continuous_log_line hc0).mul
      (continuous_integrand_line s₀ hc0 hc)).neg).aestronglyMeasurable
  · refine Eventually.of_forall fun x s hs => ?_
    rw [norm_mul, norm_neg, norm_rsOmega, one_mul, norm_neg]
    obtain ⟨h1, h2⟩ := abs_re_le_of_mem_ball hs
    exact norm_log_mul_integrand_line_le h1 h2 hc0 hc x
  · exact (integrable_exp_neg_mul_sq (by positivity)).const_mul K
  · refine Eventually.of_forall fun x s _ => ?_
    exact (hasDerivAt_integrand (line_ne_zero hc0 x) s).const_mul (-ω)

/-- The Riemann–Siegel integral is an entire function of `s`. -/
theorem differentiable_rsIntegral {c : ℝ} (hc0 : 0 < c) (hc : ∀ n : ℤ, c ≠ n) :
    Differentiable ℂ fun s => rsIntegral s c :=
  fun s => (hasDerivAt_rsIntegral s hc0 hc).differentiableAt

end RiemannSiegel
