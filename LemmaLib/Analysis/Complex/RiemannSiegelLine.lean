/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.Analysis.Complex.MordellIntegral

/-!
# Integrals along Riemann–Siegel lines

A *Riemann–Siegel line* is a line `u = c - ω x` (`x : ℝ`) through a real point `c` in the
direction `-ω = exp (5 π i / 4)`; it is the set of `u` with `Re u - Im u = c`. This file proves the
two contour-shift results for integrals `∫ -ω F (c - ω x) dx` along such lines, for integrands
with Gaussian decay on the closed strip `c ≤ Re u - Im u ≤ c'`:

* `Complex.integral_rsLine_eq` : the integral does not change when the line moves across a
  region where the integrand is holomorphic;
* `Complex.integral_rsLine_sub_eq_of_pole` : moving the line from `c` to `c'` across a simple pole
  `p` of `N u / (u - p)` subtracts `2 π i N p`.

Both are the strip lemmas of `LemmaLib.Analysis.Complex.ContourShift` transported through the
change of variables `u = c - ω ξ`, which sends the horizontal strip `0 ≤ Im ξ ≤ (c' - c) √2/2` to
the strip between the two lines.
-/

public section

open Complex Real Set Filter Topology MeasureTheory

local notation "ω" => Complex.rsOmega

namespace Complex

theorem re_sub_im_sub_rsOmega_mul (c : ℝ) (v : ℂ) :
    ((c : ℂ) - ω * v).re - ((c : ℂ) - ω * v).im = c + Real.sqrt 2 * v.im := by
  rw [rsOmega_eq]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, add_re, add_im, I_re, I_im]
  ring

theorem im_sub_rsOmega_mul (c : ℝ) (v : ℂ) :
    ((c : ℂ) - ω * v).im = -(Real.sqrt 2 / 2) * (v.re + v.im) := by
  rw [rsOmega_eq]
  simp only [sub_im, ofReal_im, mul_re, mul_im, add_re, add_im, I_re, I_im, ofReal_re]
  ring

/-- The Gaussian bound `exp (-a (Im u)²)` on the strip, in the coordinate `ξ` with
`u = c - ω ξ`, is dominated by a Gaussian in `Re ξ`. -/
theorem exp_neg_mul_im_sq_le {a : ℝ} (ha : 0 < a) {β : ℝ} (c : ℝ) {v : ℂ} (hv : |v.im| ≤ β) :
    Real.exp (-a * ((c : ℂ) - ω * v).im ^ 2) ≤
      Real.exp (a * β ^ 2 / 2) * Real.exp (-(a / 4) * v.re ^ 2) := by
  rw [← Real.exp_add, im_sub_rsOmega_mul]
  apply Real.exp_le_exp.2
  have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := sqrt_two_div_two_sq
  have hβ : v.im ^ 2 ≤ β ^ 2 := by
    have := abs_nonneg v.im
    calc v.im ^ 2 = |v.im| ^ 2 := (sq_abs _).symm
      _ ≤ β ^ 2 := by gcongr
  have key : v.re ^ 2 / 2 - v.im ^ 2 ≤ (v.re + v.im) ^ 2 := by
    nlinarith [sq_nonneg (v.re + 2 * v.im)]
  calc -a * ((-(Real.sqrt 2 / 2) * (v.re + v.im)) ^ 2)
      = -a * ((Real.sqrt 2 / 2) ^ 2 * (v.re + v.im) ^ 2) := by ring
    _ = -(a / 2) * (v.re + v.im) ^ 2 := by rw [h2]; ring
    _ ≤ -(a / 2) * (v.re ^ 2 / 2 - v.im ^ 2) := by
        apply mul_le_mul_of_nonpos_left key; linarith
    _ ≤ a * β ^ 2 / 2 + -(a / 4) * v.re ^ 2 := by nlinarith

/-- The change of variables between two Riemann–Siegel lines: `c' - ω x = c - ω (x + d)` with
`d = (c - c') conj ω`. -/
theorem rsLine_shift_eq (c c' : ℝ) (x : ℂ) :
    (c' : ℂ) - ω * x = c - ω * (x + (c - c') * (starRingEnd ℂ) ω) := by
  have := conj_rsOmega_mul
  linear_combination ((c : ℂ) - c') * this

theorem im_sub_mul_conj_rsOmega (c c' : ℝ) :
    (((c : ℂ) - c') * (starRingEnd ℂ) ω).im = (c' - c) * (Real.sqrt 2 / 2) := by
  rw [show ((c : ℂ) - c') = ((c - c' : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul,
    conj_rsOmega_im]
  ring

/-- Shifting a Riemann–Siegel line across a region where the integrand is holomorphic with
Gaussian decay: `∫ -ω F (c' - ω x) dx = ∫ -ω F (c - ω x) dx`. -/
theorem integral_rsLine_eq {F : ℂ → ℂ} {c c' a C : ℝ} (hcc' : c ≤ c') (ha : 0 < a)
    (hF : ∀ u : ℂ, u.re - u.im ∈ Icc c c' → DifferentiableAt ℂ F u)
    (hbound : ∀ u : ℂ, u.re - u.im ∈ Icc c c' → ‖F u‖ ≤ C * Real.exp (-a * u.im ^ 2)) :
    ∫ x : ℝ, -ω * F (c' - ω * x) = ∫ x : ℝ, -ω * F (c - ω * x) := by
  set d : ℂ := ((c : ℂ) - c') * (starRingEnd ℂ) ω with hd
  set β : ℝ := (c' - c) * (Real.sqrt 2 / 2) with hβ
  have hdim : d.im = β := im_sub_mul_conj_rsOmega c c'
  have hβ0 : 0 ≤ β := by rw [hβ]; have := Real.sqrt_nonneg 2; nlinarith
  set G : ℂ → ℂ := fun v => -ω * F (c - ω * v) with hG
  have hmem : ∀ v : ℂ, v.im ∈ uIcc 0 d.im → ((c : ℂ) - ω * v).re - ((c : ℂ) - ω * v).im ∈
      Icc c c' := by
    intro v hv
    rw [hdim, uIcc_of_le hβ0] at hv
    rw [re_sub_im_sub_rsOmega_mul]
    have hs : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
      rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num)]; norm_num
    constructor
    · nlinarith [Real.sqrt_nonneg 2, hv.1]
    · have := hv.2
      rw [hβ] at this
      nlinarith [Real.sqrt_nonneg 2]
  have key := integral_add_eq_integral (F := G) (c := d) (a := a / 4)
    (C := C * Real.exp (a * β ^ 2 / 2)) (by positivity)
    (fun v hv => by
      have h1 : DifferentiableAt ℂ (fun v : ℂ => (c : ℂ) - ω * v) v := by fun_prop
      exact ((hF _ (hmem v hv)).comp v h1).const_mul _)
    (fun v hv => by
      rw [hG]
      simp only []
      rw [norm_mul, norm_neg, norm_rsOmega, one_mul]
      have hvim : |v.im| ≤ β := by
        rw [hdim, uIcc_of_le hβ0] at hv
        exact abs_le.2 ⟨by linarith [hv.1], hv.2⟩
      calc ‖F (c - ω * v)‖ ≤ C * Real.exp (-a * ((c : ℂ) - ω * v).im ^ 2) :=
            hbound _ (hmem v hv)
        _ ≤ C * (Real.exp (a * β ^ 2 / 2) * Real.exp (-(a / 4) * v.re ^ 2)) := by
            have hC : 0 ≤ C :=
              nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hbound c (by simp [hcc'])))
                (Real.exp_pos _)
            exact mul_le_mul_of_nonneg_left (exp_neg_mul_im_sq_le ha c hvim) hC
        _ = C * Real.exp (a * β ^ 2 / 2) * Real.exp (-(a / 4) * v.re ^ 2) := by ring)
  have e : ∀ x : ℝ, G (x + d) = -ω * F (c' - ω * x) := by
    intro x; rw [hG]; simp only []; rw [rsLine_shift_eq c c' x]
  simp_rw [e] at key
  exact key

/-- Crossing a simple pole with a Riemann–Siegel line. If `N` is holomorphic with Gaussian decay
on the closed strip `c ≤ Re u - Im u ≤ c'` and `c < Re p - Im p < c'`, then
`∫ -ω N (c' - ω x) / (c' - ω x - p) dx - ∫ -ω N (c - ω x) / (c - ω x - p) dx = -2 π i N p`. -/
theorem integral_rsLine_sub_eq_of_pole {N : ℂ → ℂ} {p : ℂ} {c c' a C : ℝ} (ha : 0 < a)
    (hcp : c < p.re - p.im) (hpc' : p.re - p.im < c')
    (hN : ∀ u : ℂ, u.re - u.im ∈ Icc c c' → DifferentiableAt ℂ N u)
    (hbound : ∀ u : ℂ, u.re - u.im ∈ Icc c c' → ‖N u‖ ≤ C * Real.exp (-a * u.im ^ 2)) :
    (∫ x : ℝ, -ω * (N (c' - ω * x) / (c' - ω * x - p))) -
      ∫ x : ℝ, -ω * (N (c - ω * x) / (c - ω * x - p)) = -2 * π * I * N p := by
  have hcc' : c < c' := hcp.trans hpc'
  set d : ℂ := ((c : ℂ) - c') * (starRingEnd ℂ) ω with hd
  set β : ℝ := (c' - c) * (Real.sqrt 2 / 2) with hβ
  have hdim : d.im = β := im_sub_mul_conj_rsOmega c c'
  have hs2 : 0 < Real.sqrt 2 / 2 := by positivity
  have hβ0 : 0 < β := by rw [hβ]; nlinarith
  set q : ℂ := ((c : ℂ) - p) * (starRingEnd ℂ) ω with hq
  have hωq : ω * q = c - p := by
    rw [hq, mul_left_comm, mul_comm ω, conj_rsOmega_mul, mul_one]
  have hqim : q.im = (p.re - p.im - c) * (Real.sqrt 2 / 2) := by
    rw [hq, mul_im, conj_rsOmega_re, conj_rsOmega_im, sub_re, sub_im, ofReal_re, ofReal_im]
    ring
  have hq0 : 0 < q.im := by rw [hqim]; nlinarith
  have hqβ : q.im < β := by rw [hqim, hβ]; nlinarith
  set G : ℂ → ℂ := fun v => N (c - ω * v) with hG
  have hmem : ∀ v : ℂ, v.im ∈ Icc 0 β → ((c : ℂ) - ω * v).re - ((c : ℂ) - ω * v).im ∈
      Icc c c' := by
    intro v hv
    rw [re_sub_im_sub_rsOmega_mul]
    have hs : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
      rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num)]; norm_num
    constructor
    · nlinarith [Real.sqrt_nonneg 2, hv.1]
    · have := hv.2
      rw [hβ] at this
      nlinarith [Real.sqrt_nonneg 2]
  have hC : 0 ≤ C :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hbound c (by simp [hcc'.le])))
      (Real.exp_pos _)
  have key := integral_div_sub_add_ofReal_mul_I_sub_integral_div_sub (N := G) (p := q) (β := β)
    (a := a / 4) (C := C * Real.exp (a * β ^ 2 / 2)) (by positivity) hq0 hqβ
    (fun v hv => by
      have h1 : DifferentiableAt ℂ (fun v : ℂ => (c : ℂ) - ω * v) v := by fun_prop
      exact (hN _ (hmem v hv)).comp v h1)
    (fun v hv => by
      have hvim : |v.im| ≤ β := abs_le.2 ⟨by linarith [hv.1], hv.2⟩
      calc ‖G v‖ ≤ C * Real.exp (-a * ((c : ℂ) - ω * v).im ^ 2) := hbound _ (hmem v hv)
        _ ≤ C * (Real.exp (a * β ^ 2 / 2) * Real.exp (-(a / 4) * v.re ^ 2)) :=
            mul_le_mul_of_nonneg_left (exp_neg_mul_im_sq_le ha c hvim) hC
        _ = C * Real.exp (a * β ^ 2 / 2) * Real.exp (-(a / 4) * v.re ^ 2) := by ring)
  -- identify the two line integrals
  have hden : ∀ v : ℂ, (c : ℂ) - ω * v - p = -ω * (v - q) := by
    intro v; rw [neg_mul, mul_sub, hωq]; ring
  have hdiv : ∀ (A v : ℂ), -ω * (A / (-ω * (v - q))) = A / (v - q) := by
    intro A v
    rw [← mul_div_assoc, mul_div_mul_left _ _ (neg_ne_zero.2 rsOmega_ne_zero)]
  have h1 : (∫ x : ℝ, -ω * (N (c - ω * x) / (c - ω * x - p))) = ∫ x : ℝ, G x / (x - q) := by
    congr 1; ext x
    rw [hden, hdiv, hG]
  have h2 : (∫ x : ℝ, -ω * (N (c' - ω * x) / (c' - ω * x - p))) =
      ∫ x : ℝ, G (x + β * I) / (x + β * I - q) := by
    have e : ∀ x : ℝ, (c' : ℂ) - ω * x = c - ω * (((x + d.re : ℝ) : ℂ) + β * I) := by
      intro x
      rw [rsLine_shift_eq c c' x]
      congr 2
      push_cast
      rw [← hdim, add_assoc, Complex.re_add_im]
    simp_rw [e]
    rw [← integral_add_right_eq_self (fun x : ℝ => G (x + β * I) / (x + β * I - q)) d.re]
    congr 1; ext x
    rw [hden, hdiv, hG]
  rw [h1, h2, key, hG]
  simp only []
  rw [show (c : ℂ) - ω * q = p by rw [hωq]; ring]

end Complex
