/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.RiemannSiegel.Integral

/-!
# An explicit bound for the Riemann–Siegel remainder integral

For `s = σ + iT` with `σ ≥ 0`, `T ≥ 0`, and a line `Re u - Im u = c` with `c > 0` at distance at
least `ρ₀` from the integers, we bound
`‖R(s, c)‖ ≤ (√2 / (4 ρ₀)) c^{-σ} 2^{σ/2} √(π / A) exp (B² / (4 A))`
with `A = π - T / (4 π c²)` and `B = √2 π c - T / (√2 c)`.

The key input is the elementary inequality `arg ((1 - y) - i y) ≤ -y + y² / (2π)` for all real
`y`, which controls `|u^{-s}| = |u|^{-σ} exp (T arg u)` along the line `u = c - ω x`.
-/

public section

open Complex Real Set Filter Topology MeasureTheory

local notation "ω" => Complex.rsOmega

namespace RiemannSiegel

/-! ### Gaussian integrals with a linear term -/

theorem exp_quadratic_eq {A : ℝ} (hA : 0 < A) (B x : ℝ) :
    Real.exp (B * x - A * x ^ 2) =
      Real.exp (-A * (x - B / (2 * A)) ^ 2) * Real.exp (B ^ 2 / (4 * A)) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

theorem integrable_exp_quadratic {A : ℝ} (hA : 0 < A) (B : ℝ) :
    Integrable (fun x : ℝ => Real.exp (B * x - A * x ^ 2)) := by
  simp_rw [exp_quadratic_eq hA B]
  exact ((integrable_exp_neg_mul_sq hA).comp_sub_right (B / (2 * A))).mul_const _

theorem integral_exp_quadratic {A : ℝ} (hA : 0 < A) (B : ℝ) :
    ∫ x : ℝ, Real.exp (B * x - A * x ^ 2) = Real.sqrt (π / A) * Real.exp (B ^ 2 / (4 * A)) := by
  simp_rw [exp_quadratic_eq hA B]
  rw [integral_mul_const, integral_sub_right_eq_self (fun x => Real.exp (-A * x ^ 2)) (B / (2 * A)),
    integral_gaussian]

/-! ### The argument along the line -/

/-- `arg ((1 - y) - i y) ≤ -y + y² / (2π)` for every real `y`. -/
theorem arg_le_of_re_im {z : ℂ} {y : ℝ} (hre : z.re = 1 - y) (him : z.im = -y) :
    arg z ≤ -y + y ^ 2 / (2 * π) := by
  have hsq : 0 ≤ y ^ 2 / (2 * π) := by positivity
  rcases lt_or_ge y 0 with hy | hy
  · -- `Re z > 0`, `Im z > 0`: `0 ≤ arg z < π/2` and `arg z ≤ tan (arg z) = Im z / Re z ≤ -y`
    have hre0 : 0 < z.re := by rw [hre]; linarith
    have him0 : 0 < z.im := by rw [him]; linarith
    have h0 : 0 ≤ arg z := arg_nonneg_iff.2 him0.le
    have h1 : arg z < π / 2 := arg_lt_pi_div_two_iff.2 (Or.inl hre0)
    have htan : Real.tan (arg z) = -y / (1 - y) := by rw [tan_arg, hre, him]
    have h2 : arg z ≤ -y / (1 - y) := by
      rcases h0.lt_or_eq with h0 | h0
      · rw [← htan]; exact (Real.lt_tan h0 h1).le
      · rw [← h0]; exact div_nonneg (by linarith) (by linarith)
    have h3 : -y / (1 - y) ≤ -y := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  rcases le_or_gt y 1 with hy1 | hy1
  · -- `Re z ≥ 0`: `arg z = arcsin (Im z / ‖z‖) = - arcsin (y / ‖z‖)` and `arcsin (y/‖z‖) ≥ y`
    have hre0 : 0 ≤ z.re := by rw [hre]; linarith
    rw [arg_of_re_nonneg hre0, him, neg_div, Real.arcsin_neg]
    have hnorm : ‖z‖ ^ 2 = 1 - 2 * y + 2 * y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
    have hn0 : 0 < ‖z‖ := by
      rcases (norm_nonneg z).lt_or_eq with h | h
      · exact h
      · have := hnorm; rw [← h] at this; nlinarith
    have hn1 : ‖z‖ ≤ 1 := by
      rw [← abs_norm, ← sq_le_one_iff_abs_le_one, hnorm]; nlinarith
    have h1 : y ≤ y / ‖z‖ := by
      rw [le_div_iff₀ hn0]; nlinarith
    have h2 : y ≤ Real.arcsin y := by
      have := Real.sin_le (Real.arcsin_nonneg.2 hy)
      rwa [Real.sin_arcsin (by linarith) hy1] at this
    have h3 := Real.arcsin_le_arcsin h1
    linarith
  · -- `Re z ≤ 0`, `Im z < 0`: `arg z ≤ -π/2 ≤ -y + y²/(2π)`
    have him0 : z.im < 0 := by rw [him]; linarith
    have h1 : arg z ≤ -(π / 2) := by
      rcases lt_or_eq_of_le (show z.re ≤ 0 by rw [hre]; linarith) with hre0 | hre0
      · rw [arg_of_re_neg_of_im_neg hre0 him0]
        linarith [Real.arcsin_le_pi_div_two ((-z).im / ‖z‖)]
      · have hz : z = -I := by
          apply Complex.ext <;> simp [hre0, him]
          linarith
        rw [hz, arg_neg_I]
    have h2 : -(π / 2) ≤ -y + y ^ 2 / (2 * π) := by
      have : -y + y ^ 2 / (2 * π) = (y - π) ^ 2 / (2 * π) - π / 2 := by
        field_simp; ring
      rw [this]
      linarith [div_nonneg (sq_nonneg (y - π)) (by positivity : (0 : ℝ) ≤ 2 * π)]
    linarith


theorem re_line (c x : ℝ) : ((c : ℂ) - ω * x).re = c - Real.sqrt 2 / 2 * x := by
  have h1 := re_sub_im_line c x
  have h2 := im_line c x
  linarith

theorem arg_line_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    arg ((c : ℂ) - ω * x) ≤
      -(Real.sqrt 2 / 2 * x / c) + (Real.sqrt 2 / 2 * x / c) ^ 2 / (2 * π) := by
  set y := Real.sqrt 2 / 2 * x / c with hy
  have hz : (c : ℂ) - ω * x = (c : ℝ) * (((1 - y : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp only [re_line, mul_re, ofReal_re, ofReal_im, add_re, add_im, mul_I_im,
        I_re, I_im, zero_mul, sub_zero, mul_zero, mul_one, hy]
      field_simp
      ring
    · simp only [im_line, mul_im, ofReal_re, ofReal_im, add_re, mul_I_re, add_im,
        I_re, I_im, zero_mul, add_zero, zero_add, mul_zero, mul_one, hy]
      field_simp
  rw [hz, arg_real_mul _ hc]
  exact arg_le_of_re_im (by simp) (by simp)

/-- `A(c, T) = π - T / (4 π c²)`, the Gaussian decay rate along the line. -/
@[expose] noncomputable def lineA (c T : ℝ) : ℝ := π - T / (4 * π * c ^ 2)

/-- `B(c, T) = √2 π c - (√2/2) T / c`, the linear coefficient along the line. -/
@[expose] noncomputable def lineB (c T : ℝ) : ℝ := Real.sqrt 2 * π * c - Real.sqrt 2 / 2 * T / c

theorem norm_sq_line (c x : ℝ) :
    ‖(c : ℂ) - ω * x‖ ^ 2 = c ^ 2 - Real.sqrt 2 * c * x + x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, re_line, im_line]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith

theorem norm_line_ge {c : ℝ} (hc : 0 < c) (x : ℝ) :
    c / Real.sqrt 2 ≤ ‖(c : ℂ) - ω * x‖ := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := by positivity
  rw [← pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero, norm_sq_line, div_pow,
    Real.sq_sqrt (by norm_num), div_le_iff₀ (by norm_num)]
  nlinarith [sq_nonneg (Real.sqrt 2 * x - c)]

/-- `|u^{-s}| ≤ c^{-σ} 2^{σ/2} exp (T (-y + y²/(2π)))` on the line `u = c - ω x`,
where `y = (√2/2) x / c`, for `σ ≥ 0` and `T ≥ 0`. -/
theorem norm_cpow_neg_line_le {s : ℂ} {c : ℝ} (hσ : 0 ≤ s.re) (hT : 0 ≤ s.im) (hc : 0 < c)
    (x : ℝ) :
    ‖((c : ℂ) - ω * x) ^ (-s)‖ ≤ c ^ (-s.re) * 2 ^ (s.re / 2) *
      Real.exp (s.im * (-(Real.sqrt 2 / 2 * x / c) + (Real.sqrt 2 / 2 * x / c) ^ 2 / (2 * π))) := by
  rw [norm_cpow_of_ne_zero (line_ne_zero hc x), neg_re, neg_im, mul_neg, Real.exp_neg,
    div_inv_eq_mul]
  have hs : 0 < Real.sqrt 2 := by positivity
  have h1 : ‖(c : ℂ) - ω * x‖ ^ (-s.re) ≤ c ^ (-s.re) * 2 ^ (s.re / 2) := by
    calc ‖(c : ℂ) - ω * x‖ ^ (-s.re) ≤ (c / Real.sqrt 2) ^ (-s.re) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (norm_line_ge hc x) (by linarith)
      _ = c ^ (-s.re) * 2 ^ (s.re / 2) := by
          rw [Real.div_rpow hc.le hs.le, Real.rpow_neg hs.le, div_inv_eq_mul, Real.sqrt_eq_rpow,
            ← Real.rpow_mul (by norm_num)]
          ring_nf
  have h2 : Real.exp (arg ((c : ℂ) - ω * x) * s.im) ≤
      Real.exp (s.im * (-(Real.sqrt 2 / 2 * x / c) + (Real.sqrt 2 / 2 * x / c) ^ 2 / (2 * π))) := by
    rw [mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (arg_line_le hc x) hT)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

theorem norm_exp_pi_I_mul_sq_line (c x : ℝ) :
    ‖cexp (π * I * ((c : ℂ) - ω * x) ^ 2)‖ =
      Real.exp (Real.sqrt 2 * π * c * x - π * x ^ 2) := by
  rw [norm_exp_pi_I_mul_sq, re_line, im_line]
  congr 1
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination (-(π * x ^ 2 / 2)) * h2

/-- The pointwise bound along the line: for `σ ≥ 0`, `T ≥ 0`, `c > 0` at distance `≥ ρ₀` from
the integers, `‖integrand s (c - ω x)‖ ≤ (√2/(4ρ₀)) c^{-σ} 2^{σ/2} exp (B x - A x²)`. -/
theorem norm_integrand_line_le' {s : ℂ} {c ρ₀ : ℝ} (hσ : 0 ≤ s.re) (hT : 0 ≤ s.im) (hc : 0 < c)
    (hρ₀ : 0 < ρ₀) (hcZ : ∀ m : ℤ, ρ₀ ≤ |c - m|) (x : ℝ) :
    ‖integrand s ((c : ℂ) - ω * x)‖ ≤ Real.sqrt 2 / (4 * ρ₀) * (c ^ (-s.re) * 2 ^ (s.re / 2)) *
      Real.exp (lineB c s.im * x - lineA c s.im * x ^ 2) := by
  have e : integrand s ((c : ℂ) - ω * x) = ((c : ℂ) - ω * x) ^ (-s) *
      cexp (π * I * ((c : ℂ) - ω * x) ^ 2) *
      (cexp (π * I * ((c : ℂ) - ω * x)) - cexp (-(π * I * ((c : ℂ) - ω * x))))⁻¹ := by
    unfold integrand kernel; ring
  rw [e, norm_mul, norm_mul, norm_exp_pi_I_mul_sq_line]
  have h1 := norm_cpow_neg_line_le hσ hT hc x
  have h3 := norm_inv_exp_sub_exp_neg_le hρ₀ (u := (c : ℂ) - ω * x)
    (fun m => by rw [re_sub_im_line]; exact hcZ m)
  have hexp : Real.exp (s.im * (-(Real.sqrt 2 / 2 * x / c) + (Real.sqrt 2 / 2 * x / c) ^ 2 /
      (2 * π))) * Real.exp (Real.sqrt 2 * π * c * x - π * x ^ 2) =
      Real.exp (lineB c s.im * x - lineA c s.im * x ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    unfold lineA lineB
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    ring_nf
    rw [show Real.sqrt 2 ^ 2 = 2 by rw [sq, h2]]
    ring
  calc ‖((c : ℂ) - ω * x) ^ (-s)‖ * Real.exp (Real.sqrt 2 * π * c * x - π * x ^ 2) *
        ‖(cexp (π * I * ((c : ℂ) - ω * x)) - cexp (-(π * I * ((c : ℂ) - ω * x))))⁻¹‖
      ≤ c ^ (-s.re) * 2 ^ (s.re / 2) *
        Real.exp (s.im * (-(Real.sqrt 2 / 2 * x / c) + (Real.sqrt 2 / 2 * x / c) ^ 2 / (2 * π))) *
        Real.exp (Real.sqrt 2 * π * c * x - π * x ^ 2) * (Real.sqrt 2 / (4 * ρ₀)) := by
        gcongr
    _ = Real.sqrt 2 / (4 * ρ₀) * (c ^ (-s.re) * 2 ^ (s.re / 2)) *
        Real.exp (lineB c s.im * x - lineA c s.im * x ^ 2) := by
        rw [← hexp]; ring

/-- The explicit bound on the Riemann–Siegel integral along the line through `c`:
`‖R(s, c)‖ ≤ (√2/(4ρ₀)) c^{-σ} 2^{σ/2} √(π/A) exp (B²/(4A))` for `σ ≥ 0`, `T ≥ 0`, `A > 0`. -/
theorem norm_rsIntegral_le {s : ℂ} {c ρ₀ : ℝ} (hσ : 0 ≤ s.re) (hT : 0 ≤ s.im) (hc : 0 < c)
    (hρ₀ : 0 < ρ₀) (hcZ : ∀ m : ℤ, ρ₀ ≤ |c - m|) (hA : 0 < lineA c s.im) :
    ‖rsIntegral s c‖ ≤ Real.sqrt 2 / (4 * ρ₀) * (c ^ (-s.re) * 2 ^ (s.re / 2)) *
      (Real.sqrt (π / lineA c s.im) * Real.exp (lineB c s.im ^ 2 / (4 * lineA c s.im))) := by
  unfold rsIntegral
  calc ‖∫ x : ℝ, -ω * integrand s ((c : ℂ) - ω * x)‖
      ≤ ∫ x : ℝ, Real.sqrt 2 / (4 * ρ₀) * (c ^ (-s.re) * 2 ^ (s.re / 2)) *
          Real.exp (lineB c s.im * x - lineA c s.im * x ^ 2) := by
        refine norm_integral_le_of_norm_le ((integrable_exp_quadratic hA _).const_mul _)
          (Filter.Eventually.of_forall fun x => ?_)
        rw [norm_mul, norm_neg, norm_rsOmega, one_mul]
        exact norm_integrand_line_le' hσ hT hc hρ₀ hcZ x
    _ = _ := by rw [integral_const_mul, integral_exp_quadratic hA]


/-! ### The bound for `Re s ≤ 0` -/

theorem norm_line_le (c x : ℝ) : ‖(c : ℂ) - ω * x‖ ≤ |c| + |x| := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_rsOmega, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

/-- `|u^{-s}| ≤ c^{-σ} exp (-σ |x| / c) exp (T (-y + y²/(2π)))` on the line `u = c - ω x` for
`σ ≤ 0` and `T ≥ 0`. -/
theorem norm_cpow_neg_line_le_of_nonpos {s : ℂ} {c : ℝ} (hσ : s.re ≤ 0) (hT : 0 ≤ s.im)
    (hc : 0 < c) (x : ℝ) :
    ‖((c : ℂ) - ω * x) ^ (-s)‖ ≤ c ^ (-s.re) * Real.exp (-s.re * |x| / c) *
      Real.exp (s.im * (-(Real.sqrt 2 / 2 * x / c) + (Real.sqrt 2 / 2 * x / c) ^ 2 / (2 * π))) := by
  rw [norm_cpow_of_ne_zero (line_ne_zero hc x), neg_re, neg_im, mul_neg, Real.exp_neg,
    div_inv_eq_mul]
  have h1 : ‖(c : ℂ) - ω * x‖ ^ (-s.re) ≤ c ^ (-s.re) * Real.exp (-s.re * |x| / c) := by
    calc ‖(c : ℂ) - ω * x‖ ^ (-s.re) ≤ (c * Real.exp (|x| / c)) ^ (-s.re) := by
          apply Real.rpow_le_rpow (norm_nonneg _) _ (by linarith)
          refine (norm_line_le c x).trans ?_
          rw [abs_of_pos hc]
          have := Real.add_one_le_exp (|x| / c)
          calc c + |x| = c * (|x| / c + 1) := by field_simp; ring
            _ ≤ c * Real.exp (|x| / c) := by gcongr
      _ = c ^ (-s.re) * Real.exp (-s.re * |x| / c) := by
          rw [Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
          ring_nf
  have h2 : Real.exp (arg ((c : ℂ) - ω * x) * s.im) ≤
      Real.exp (s.im * (-(Real.sqrt 2 / 2 * x / c) + (Real.sqrt 2 / 2 * x / c) ^ 2 / (2 * π))) := by
    rw [mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (arg_line_le hc x) hT)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

/-- `λ |x| ≤ λ² / A + (A/4) x²` for `A > 0`. -/
theorem mul_abs_le_div_add_sq {A : ℝ} (hA : 0 < A) (l x : ℝ) :
    l * |x| ≤ l ^ 2 / A + A / 4 * x ^ 2 := by
  have h : 0 ≤ (Real.sqrt A / 2 * |x| - l / Real.sqrt A) ^ 2 := sq_nonneg _
  have hs : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  have hs0 : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have e : (Real.sqrt A / 2 * |x| - l / Real.sqrt A) ^ 2 =
      A / 4 * x ^ 2 - l * |x| + l ^ 2 / A := by
    have hx : |x| ^ 2 = x ^ 2 := sq_abs x
    have hs4 : Real.sqrt A ^ 4 = A ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hs]
    field_simp
    ring_nf
    rw [hs, hs4, hx]
    ring
  linarith

/-- The pointwise bound along the line for `σ ≤ 0`:
`‖integrand s (c - ω x)‖ ≤ (√2/(4ρ₀)) c^{-σ} exp (σ²/(A c²)) exp (B x - (3A/4) x²)`. -/
theorem norm_integrand_line_le_of_nonpos {s : ℂ} {c ρ₀ : ℝ} (hσ : s.re ≤ 0) (hT : 0 ≤ s.im)
    (hc : 0 < c) (hρ₀ : 0 < ρ₀) (hcZ : ∀ m : ℤ, ρ₀ ≤ |c - m|) (hA : 0 < lineA c s.im) (x : ℝ) :
    ‖integrand s ((c : ℂ) - ω * x)‖ ≤
      Real.sqrt 2 / (4 * ρ₀) * (c ^ (-s.re) * Real.exp (s.re ^ 2 / (lineA c s.im * c ^ 2))) *
        Real.exp (lineB c s.im * x - 3 / 4 * lineA c s.im * x ^ 2) := by
  have e : integrand s ((c : ℂ) - ω * x) = ((c : ℂ) - ω * x) ^ (-s) *
      cexp (π * I * ((c : ℂ) - ω * x) ^ 2) *
      (cexp (π * I * ((c : ℂ) - ω * x)) - cexp (-(π * I * ((c : ℂ) - ω * x))))⁻¹ := by
    unfold integrand kernel; ring
  rw [e, norm_mul, norm_mul, norm_exp_pi_I_mul_sq_line]
  have h1 := norm_cpow_neg_line_le_of_nonpos hσ hT hc x
  have h3 := norm_inv_exp_sub_exp_neg_le hρ₀ (u := (c : ℂ) - ω * x)
    (fun m => by rw [re_sub_im_line]; exact hcZ m)
  have hexp : Real.exp (s.im * (-(Real.sqrt 2 / 2 * x / c) + (Real.sqrt 2 / 2 * x / c) ^ 2 /
      (2 * π))) * Real.exp (Real.sqrt 2 * π * c * x - π * x ^ 2) =
      Real.exp (lineB c s.im * x - lineA c s.im * x ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    unfold lineA lineB
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    ring_nf
    rw [show Real.sqrt 2 ^ 2 = 2 by rw [sq, h2]]
    ring
  have hamgm : Real.exp (-s.re * |x| / c) * Real.exp (lineB c s.im * x - lineA c s.im * x ^ 2) ≤
      Real.exp (s.re ^ 2 / (lineA c s.im * c ^ 2)) *
        Real.exp (lineB c s.im * x - 3 / 4 * lineA c s.im * x ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have := mul_abs_le_div_add_sq hA (-s.re / c) x
    have e1 : (-s.re / c) ^ 2 / lineA c s.im = s.re ^ 2 / (lineA c s.im * c ^ 2) := by
      field_simp
    have e2 : -s.re * |x| / c = -s.re / c * |x| := by ring
    rw [e2]
    linarith
  calc ‖((c : ℂ) - ω * x) ^ (-s)‖ * Real.exp (Real.sqrt 2 * π * c * x - π * x ^ 2) *
        ‖(cexp (π * I * ((c : ℂ) - ω * x)) - cexp (-(π * I * ((c : ℂ) - ω * x))))⁻¹‖
      ≤ c ^ (-s.re) * Real.exp (-s.re * |x| / c) *
        Real.exp (s.im * (-(Real.sqrt 2 / 2 * x / c) + (Real.sqrt 2 / 2 * x / c) ^ 2 / (2 * π))) *
        Real.exp (Real.sqrt 2 * π * c * x - π * x ^ 2) * (Real.sqrt 2 / (4 * ρ₀)) := by
        gcongr
    _ = Real.sqrt 2 / (4 * ρ₀) * c ^ (-s.re) * (Real.exp (-s.re * |x| / c) *
        Real.exp (lineB c s.im * x - lineA c s.im * x ^ 2)) := by
        rw [← hexp]; ring
    _ ≤ Real.sqrt 2 / (4 * ρ₀) * c ^ (-s.re) * (Real.exp (s.re ^ 2 / (lineA c s.im * c ^ 2)) *
        Real.exp (lineB c s.im * x - 3 / 4 * lineA c s.im * x ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- The explicit bound on the Riemann–Siegel integral for `σ ≤ 0`:
`‖R(s, c)‖ ≤ (√2/(4ρ₀)) c^{-σ} exp (σ²/(A c²)) √(π/(3A/4)) exp (B²/(3A))`. -/
theorem norm_rsIntegral_le_of_re_nonpos {s : ℂ} {c ρ₀ : ℝ} (hσ : s.re ≤ 0) (hT : 0 ≤ s.im)
    (hc : 0 < c) (hρ₀ : 0 < ρ₀) (hcZ : ∀ m : ℤ, ρ₀ ≤ |c - m|) (hA : 0 < lineA c s.im) :
    ‖rsIntegral s c‖ ≤
      Real.sqrt 2 / (4 * ρ₀) * (c ^ (-s.re) * Real.exp (s.re ^ 2 / (lineA c s.im * c ^ 2))) *
        (Real.sqrt (π / (3 / 4 * lineA c s.im)) *
          Real.exp (lineB c s.im ^ 2 / (4 * (3 / 4 * lineA c s.im)))) := by
  have hA' : 0 < 3 / 4 * lineA c s.im := by positivity
  unfold rsIntegral
  calc ‖∫ x : ℝ, -ω * integrand s ((c : ℂ) - ω * x)‖
      ≤ ∫ x : ℝ, Real.sqrt 2 / (4 * ρ₀) *
          (c ^ (-s.re) * Real.exp (s.re ^ 2 / (lineA c s.im * c ^ 2))) *
          Real.exp (lineB c s.im * x - 3 / 4 * lineA c s.im * x ^ 2) := by
        refine norm_integral_le_of_norm_le ((integrable_exp_quadratic hA' _).const_mul _)
          (Filter.Eventually.of_forall fun x => ?_)
        rw [norm_mul, norm_neg, norm_rsOmega, one_mul]
        exact norm_integrand_line_le_of_nonpos hσ hT hc hρ₀ hcZ hA x
    _ = _ := by rw [integral_const_mul, integral_exp_quadratic hA']

/-! ### Independence of the line within `(n, n + 1)` -/

theorem strip_dist_of_mem_Ioo (c c' : ℝ) (n : ℕ) :
    ∀ κ ∈ Icc c c', ∀ m : ℤ, min (c - n) (n + 1 - c') ≤ |κ - m| := by
  intro κ hκ m
  rcases le_or_gt m n with h | h
  · have : (m : ℝ) ≤ n := by exact_mod_cast h
    refine (min_le_left _ _).trans (le_trans ?_ (le_abs_self _)); linarith [hκ.1]
  · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    refine (min_le_right _ _).trans (le_trans ?_ (neg_le_abs _)); linarith [hκ.2]

theorem sin_pi_mul_ne_zero_of_dist {u : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ m : ℤ, ρ ≤ |u.re - u.im - m|) : Complex.sin (π * u) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h
  have hu' : u = k := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [mul_comm] at hk
    exact mul_right_cancel₀ hπ hk
  have := hu k
  rw [hu'] at this
  simp at this
  linarith

theorem differentiableAt_integrand_of_dist {s u : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hu0 : 0 < u.re - u.im)
    (hu : ∀ m : ℤ, ρ ≤ |u.re - u.im - m|) : DifferentiableAt ℂ (integrand s) u := by
  unfold integrand kernel
  have h1 : DifferentiableAt ℂ (fun u : ℂ => u ^ (-s)) u :=
    differentiableAt_id.cpow_const (mem_slitPlane_of_re_sub_im_pos hu0)
  have h2 : cexp (π * I * u) - cexp (-(π * I * u)) ≠ 0 := by
    rw [exp_sub_exp_neg_eq_two_I_sin]
    exact mul_ne_zero (by simp) (sin_pi_mul_ne_zero_of_dist hρ hu)
  have h3 : DifferentiableAt ℂ (fun u : ℂ => cexp (π * I * u ^ 2)) u := by fun_prop
  have h4 : DifferentiableAt ℂ (fun u : ℂ => cexp (π * I * u) - cexp (-(π * I * u))) u := by
    fun_prop
  exact h1.mul (h3.div h4 h2)

/-- The Riemann–Siegel integral does not depend on the line as long as it stays within
`(n, n + 1)`. -/
theorem rsIntegral_eq_of_mem_Ioo (s : ℂ) {c c' : ℝ} {n : ℕ} (hcn : (n : ℝ) < c)
    (hcn' : c < n + 1) (hnc' : (n : ℝ) < c') (hc'n : c' < n + 1) :
    rsIntegral s c = rsIntegral s c' := by
  wlog hcc' : c ≤ c' generalizing c c'
  · exact (this hnc' hc'n hcn hcn' (le_of_not_ge hcc')).symm
  set ρ := min (c - n) (n + 1 - c') with hρ
  have hρ0 : 0 < ρ := lt_min (by linarith) (by linarith)
  have hc0 : 0 < c := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hstrip := strip_dist_of_mem_Ioo c c' n
  unfold rsIntegral
  refine (integral_rsLine_eq (C := boundConst |s.re| |s.im| c c' ρ) hcc' Real.pi_pos
    (fun u hu => ?_) (fun u hu => ?_)).symm
  · exact differentiableAt_integrand_of_dist hρ0 (hc0.trans_le hu.1) (hstrip _ hu)
  · exact norm_integrand_le (le_refl _) (le_refl _) hc0 hρ0 hstrip hu

end RiemannSiegel
