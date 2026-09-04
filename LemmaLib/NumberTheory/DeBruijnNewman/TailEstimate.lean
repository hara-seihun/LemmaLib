/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.Tail
public import LemmaLib.NumberTheory.DeBruijnNewman.EffectiveApproximation

/-!
# The Riemann–Siegel tail estimate with an explicit constant

This file turns the bound `norm_tail_le` of `LemmaLib.NumberTheory.DeBruijnNewman.Tail` into
numbers on the region of Polymath Theorem 1.3: for `0 ≤ t ≤ 1/2`, `0 ≤ y ≤ 1` and `x ≥ 200`, with
`T = x/2`, `a = √(x/(4π))`, `N = cutoff t x` and the line through `c = clampC N a` (the point of
`[N + 1/4, N + 3/4]` nearest to the saddle `a`),

* `tailIntegral t T c σ ≤ 8.19` for `0 ≤ σ ≤ 1` (`tailIntegral_le`), and
* `‖M₀(iT)‖ ≤ exp (tπ²/64) ‖M₀(i(T + πt/8))‖ · 1.081` (`norm_M₀_axis_le_shift`),

so the tail is at most `20` times the bound Polymath's Proposition 6.3 would give
(`tailEstimateWith : TailEstimateWith 20`), and Theorem 1.3 holds with `e_{C,0}` multiplied by
`20` (`effectiveApproximationWith : EffectiveApproximationWith 20`).
-/

public section

open Complex Real Set Filter Topology MeasureTheory RiemannSiegel

namespace DeBruijnNewman

/-! ### Numerical helpers -/

/-- `exp x ≤ P₇(b)` for `x ≤ b ≤ 1`, with `P₇` the degree-`7` Taylor polynomial plus its
remainder term. -/
theorem exp_le_taylor {x b : ℝ} (hx : x ≤ b) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp x ≤ ∑ m ∈ Finset.range 7, b ^ m / m.factorial + b ^ 7 * 8 / (Nat.factorial 7 * 7) := by
  refine (Real.exp_le_exp.2 hx).trans ((Real.exp_bound' hb0 hb1 (n := 7) (by norm_num)).trans_eq ?_)
  norm_num

theorem exp_le_of_le {x b q : ℝ} (hx : x ≤ b) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hq : ∑ m ∈ Finset.range 7, b ^ m / m.factorial + b ^ 7 * 8 / (Nat.factorial 7 * 7) ≤ q) :
    Real.exp x ≤ q :=
  (exp_le_taylor hx hb0 hb1).trans hq

/-! ### `M₀` along the imaginary axis -/

/-- Moving up the imaginary axis by `δ ≥ 0` decreases `‖M₀‖` by at most `exp (δπ/4 + δ²/(4T-12))`. -/
theorem norm_M₀_axis_le {T δ : ℝ} (hT : 3 < T) (hδ : 0 ≤ δ) :
    ‖M₀ ((T : ℂ) * I)‖ ≤
      ‖M₀ (((T + δ : ℝ) : ℂ) * I)‖ * Real.exp (δ * π / 4 + δ ^ 2 / (4 * T - 12)) := by
  set z : ℂ := (T : ℂ) * I with hz
  set h : ℂ := (δ : ℂ) * I with hh
  have hzim : ∀ τ : ℝ, (z + τ * h).im = T + τ * δ := fun τ => by simp [hz, hh]
  have hτδ : ∀ τ ∈ Icc (0 : ℝ) 1, 0 ≤ τ * δ := fun τ hτ => mul_nonneg hτ.1 hδ
  have hg : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt logM₀ (alpha (z + τ * h)) (z + τ * h) :=
    fun τ hτ => hasDerivAt_logM₀ (by rw [hzim]; linarith [hτδ τ hτ])
  have hα : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt alpha (alpha' (z + τ * h)) (z + τ * h) :=
    fun τ hτ => hasDerivAt_alpha (by rw [hzim]; linarith [hτδ τ hτ])
  have hb : ∀ τ ∈ Icc (0 : ℝ) 1, ‖alpha' (z + τ * h)‖ ≤ 1 / (2 * T - 6) := by
    intro τ hτ
    have h1 := norm_alpha'_le (s := z + τ * h) (by rw [hzim]; linarith [hτδ τ hτ])
    rw [hzim] at h1
    refine h1.trans (one_div_le_one_div_of_le (by linarith) (by linarith [hτδ τ hτ]))
  have hg' := norm_sub_le_of_hasDerivAt_segment hα hb
  have key := norm_taylor_two_le hg (K := 1 / (2 * T - 6))
    (fun τ hτ => (hg' τ hτ).trans_eq (by ring))
  have hre := (abs_le.1 (Complex.abs_re_le_norm (logM₀ (z + h) - logM₀ z - h * alpha z))).1.trans'
    (neg_le_neg key)
  have hnh : ‖h‖ = δ := by rw [hh, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hδ]
  rw [hnh, sub_re, sub_re] at hre
  have him : (h * alpha z).re = -(δ * (alpha z).im) := by
    rw [hh, mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re]; ring
  have hIm : (alpha z).im ≤ π / 4 := by
    rw [hz, im_alpha_axis (by linarith)]
    have : 0 ≤ T / (1 + T ^ 2) := by positivity
    have : 0 ≤ 1 / (2 * T) := by positivity
    linarith
  have e : (((T + δ : ℝ) : ℂ) * I) = z + h := by rw [hz, hh]; push_cast; ring
  have h1 : (z).im ≠ 0 := by rw [hz]; simp; linarith
  have h2 : (z + h).im ≠ 0 := by rw [hz, hh]; simp; linarith
  rw [e, norm_M₀ (ne_zero_of_im_ne_zero h1) (ne_one_of_im_ne_zero h1),
    norm_M₀ (ne_zero_of_im_ne_zero h2) (ne_one_of_im_ne_zero h2), ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h3 : 0 < 2 * T - 6 := by linarith
  have e2 : 1 / (2 * T - 6) * δ ^ 2 / 2 = δ ^ 2 / (4 * T - 12) := by
    rw [show 4 * T - 12 = 2 * (2 * T - 6) by ring]; field_simp
  rw [him] at hre
  nlinarith [mul_le_mul_of_nonneg_left hIm hδ]

/-- `‖M₀(iT)‖ ≤ exp (tπ²/64) ‖M₀(i(T + πt/8))‖ · 1.081` for `T ≥ 100`,
`0 ≤ t ≤ 1/2`. -/
theorem norm_M₀_axis_le_shift {t T : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hT : 100 ≤ T) :
    ‖M₀ ((T : ℂ) * I)‖ ≤
      Real.exp (t * π ^ 2 / 64) * ‖M₀ (((T + π * t / 8 : ℝ) : ℂ) * I)‖ * 1.081 := by
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  have hδ : 0 ≤ π * t / 8 := by positivity
  have h := norm_M₀_axis_le (T := T) (δ := π * t / 8) (by linarith) hδ
  refine h.trans ?_
  rw [mul_comm (Real.exp _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hδ1 : π * t / 8 ≤ 0.2 := by nlinarith
  have hsq : (π * t / 8) ^ 2 / (4 * T - 12) ≤ 0.00011 := by
    rw [div_le_iff₀ (by linarith)]
    have : (π * t / 8) ^ 2 ≤ 0.04 := by nlinarith
    nlinarith
  have hlin : π * t / 8 * π / 4 ≤ t * π ^ 2 / 64 + t * π ^ 2 / 64 := by nlinarith
  have hexp : Real.exp (t * π ^ 2 / 64 + 0.00011) ≤ 1.081 := by
    refine exp_le_of_le (b := 0.0777) ?_ (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    have : π ^ 2 ≤ 9.9225 := by nlinarith
    have : t * π ^ 2 ≤ 0.5 * 9.9225 := by nlinarith
    linarith
  calc Real.exp (π * t / 8 * π / 4 + (π * t / 8) ^ 2 / (4 * T - 12))
      ≤ Real.exp (t * π ^ 2 / 64 + (t * π ^ 2 / 64 + 0.00011)) := by
        apply Real.exp_le_exp.2; linarith
    _ = Real.exp (t * π ^ 2 / 64) * Real.exp (t * π ^ 2 / 64 + 0.00011) := Real.exp_add _ _
    _ ≤ Real.exp (t * π ^ 2 / 64) * 1.081 := by gcongr


/-! ### The Gaussian integrals `gaussJ` -/

/-- A uniform bound on `gaussJ t σ α β` for `0 ≤ t ≤ 1/2`, `0 ≤ σ ≤ 1`, `|α| ≤ αmax` and
`0 ≤ β ≤ βmax < 2`. -/
theorem gaussJ_le {t σ α β αmax βmax : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hβ0 : 0 ≤ β) (hβ : β ≤ βmax) (hα : |α| ≤ αmax) (hβmax : βmax < 2) :
    gaussJ t σ α β ≤
      Real.exp (αmax + βmax + (αmax + 2 * βmax) ^ 2 / (8 * (1 - βmax / 2))) /
        Real.sqrt (1 - βmax / 2) := by
  unfold gaussJ
  have hαmax : 0 ≤ αmax := (abs_nonneg α).trans hα
  have hD : 1 - βmax / 2 ≤ 1 - β * t := by nlinarith
  have hD0 : 0 < 1 - βmax / 2 := by linarith
  have hD0' : 0 < 1 - β * t := by linarith
  have h1 : α * σ ≤ αmax := by
    calc α * σ ≤ |α| * σ := mul_le_mul_of_nonneg_right (le_abs_self α) hσ0
      _ ≤ αmax * 1 := mul_le_mul hα hσ1 hσ0 hαmax
      _ = αmax := mul_one _
  have h2 : β * σ ^ 2 ≤ βmax := by
    have : σ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have h3 : (α + 2 * β * σ) ^ 2 ≤ (αmax + 2 * βmax) ^ 2 := by
    have : |α + 2 * β * σ| ≤ αmax + 2 * βmax := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * β * σ)]
      nlinarith
    exact sq_le_sq' (by linarith [abs_le.1 this]) (by linarith [abs_le.1 this])
  have h4 : t * (α + 2 * β * σ) ^ 2 / (4 * (1 - β * t)) ≤
      (αmax + 2 * βmax) ^ 2 / (8 * (1 - βmax / 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 : t * (α + 2 * β * σ) ^ 2 ≤ 1 / 2 * (αmax + 2 * βmax) ^ 2 :=
      mul_le_mul ht h3 (sq_nonneg _) (by norm_num)
    have h6 := mul_le_mul_of_nonneg_right h5 (by linarith : (0 : ℝ) ≤ 8 * (1 - βmax / 2))
    have h7 := mul_le_mul_of_nonneg_left hD
      (by positivity : (0 : ℝ) ≤ 4 * (αmax + 2 * βmax) ^ 2)
    nlinarith
  have hsq : Real.sqrt (1 - βmax / 2) ≤ Real.sqrt (1 - β * t) := Real.sqrt_le_sqrt hD
  have hsq0 : 0 < Real.sqrt (1 - βmax / 2) := Real.sqrt_pos.2 hD0
  have hexp : Real.exp (α * σ + β * σ ^ 2 + t * (α + 2 * β * σ) ^ 2 / (4 * (1 - β * t))) ≤
      Real.exp (αmax + βmax + (αmax + 2 * βmax) ^ 2 / (8 * (1 - βmax / 2))) :=
    Real.exp_le_exp.2 (by linarith)
  calc Real.exp (α * σ + β * σ ^ 2 + t * (α + 2 * β * σ) ^ 2 / (4 * (1 - β * t))) /
        Real.sqrt (1 - β * t)
      ≤ Real.exp (α * σ + β * σ ^ 2 + t * (α + 2 * β * σ) ^ 2 / (4 * (1 - β * t))) /
        Real.sqrt (1 - βmax / 2) := div_le_div_of_nonneg_left (Real.exp_pos _).le hsq0 hsq
    _ ≤ _ := div_le_div_of_nonneg_right hexp hsq0.le

/-! ### The tail integral, numerically -/

/-- `tailIntegral t T c σ ≤ 8.2` on the region, given the geometric inputs on the line through
`c`: `lineA c T ≥ 2.572`, `lineB c T² ≤ 5.443`, `c ≥ 3.739` and `|Re α(iT) - log c| ≤ 0.065`. -/
theorem tailIntegral_le {t T c σ : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hT : 100 ≤ T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hA : 2.572 ≤ lineA c T) (hB : lineB c T ^ 2 ≤ 5.443)
    (hc : 3.739 ≤ c) (hα : |(alpha ((T : ℂ) * I)).re - Real.log c| ≤ 0.065) :
    tailIntegral t T c σ ≤ 8.2 := by
  unfold tailIntegral
  have hpi := Real.pi_lt_d4
  have hpi' := Real.pi_gt_d4
  have hA0 : 0 < lineA c T := by linarith
  -- the prefactors
  have e1 : Real.exp (1 / (6 * (T - 0.8))) ≤ 1.0018 := by
    refine exp_le_of_le (b := 0.0017) ?_ (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    rw [div_le_iff₀ (by linarith)]; linarith
  have e2 : Real.sqrt 2 ≤ 1.41422 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have e3 : Real.sqrt (π / lineA c T) ≤ 1.1053 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ hA0]
    have : (1.1053 : ℝ) ^ 2 = 1.22168809 := by norm_num
    rw [this]; linarith
  have e4 : Real.exp (lineB c T ^ 2 / (4 * lineA c T)) ≤ 1.6975 := by
    refine exp_le_of_le (b := 0.5291) ?_ (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e5 : Real.exp (lineB c T ^ 2 / (3 * lineA c T)) ≤ 2.025 := by
    refine exp_le_of_le (b := 0.7055) ?_ (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e6 : 2 / Real.sqrt 3 ≤ 1.1548 := by
    have : (1.732 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [div_le_iff₀ (by positivity)]; linarith
  -- the two Gaussian integrals
  have hβ1 : 1 / (4 * T - 12) ≤ 0.00258 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hβ1' : 0 ≤ 1 / (4 * T - 12) := one_div_nonneg.2 (by linarith)
  have hAc : 1 / (lineA c T * c ^ 2) ≤ 0.0279 := by
    rw [div_le_iff₀ (mul_pos hA0 (pow_pos (by linarith) 2))]
    have h1 : (3.739 : ℝ) ^ 2 ≤ c ^ 2 := by gcongr
    have h2 : (2.572 : ℝ) * 3.739 ^ 2 ≤ lineA c T * c ^ 2 := by gcongr
    linarith
  have hα1 : |(alpha ((T : ℂ) * I)).re - Real.log c + Real.log 2 / 2| ≤ 0.4116 := by
    have hl2 := Real.log_two_lt_d9
    have hl2' := Real.log_two_gt_d9
    rw [abs_le] at hα ⊢; constructor <;> linarith
  have J1 := gaussJ_le (αmax := 0.4116) (βmax := 0.00258) ht0 ht hσ0 hσ1 hβ1' hβ1 hα1
    (by norm_num)
  have J1' : Real.exp (0.4116 + 0.00258 + (0.4116 + 2 * 0.00258) ^ 2 / (8 * (1 - 0.00258 / 2))) /
      Real.sqrt (1 - 0.00258 / 2) ≤ 1.548 := by
    have h1 : Real.exp (0.4116 + 0.00258 + (0.4116 + 2 * 0.00258) ^ 2 /
        (8 * (1 - 0.00258 / 2))) ≤ 1.5466 :=
      exp_le_of_le (b := 0.436) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ])
    have h2 : (0.99935 : ℝ) ≤ Real.sqrt (1 - 0.00258 / 2) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [div_le_iff₀ (by positivity)]; linarith
  have hβ2' : 0 ≤ 1 / (4 * T - 12) + 1 / (lineA c T * c ^ 2) := by
    have : 0 ≤ 1 / (lineA c T * c ^ 2) := by positivity
    linarith
  have J2 := gaussJ_le (αmax := 0.065) (βmax := 0.0305)
    (β := 1 / (4 * T - 12) + 1 / (lineA c T * c ^ 2)) ht0 ht hσ0 hσ1 hβ2' (by linarith) hα
    (by norm_num)
  have J2' : Real.exp (0.065 + 0.0305 + (0.065 + 2 * 0.0305) ^ 2 / (8 * (1 - 0.0305 / 2))) /
      Real.sqrt (1 - 0.0305 / 2) ≤ 1.1112 := by
    have h1 : Real.exp (0.065 + 0.0305 + (0.065 + 2 * 0.0305) ^ 2 /
        (8 * (1 - 0.0305 / 2))) ≤ 1.1026 :=
      exp_le_of_le (b := 0.0976) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ])
    have h2 : (0.9923 : ℝ) ≤ Real.sqrt (1 - 0.0305 / 2) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [div_le_iff₀ (by positivity)]; linarith
  have hJ1 := J1.trans J1'
  have hJ2 := J2.trans J2'
  -- assemble
  have hJ1n : 0 ≤ gaussJ t σ ((alpha ((T : ℂ) * I)).re - Real.log c + Real.log 2 / 2)
      (1 / (4 * T - 12)) := by unfold gaussJ; positivity
  have hJ2n : 0 ≤ gaussJ t σ ((alpha ((T : ℂ) * I)).re - Real.log c)
      (1 / (4 * T - 12) + 1 / (lineA c T * c ^ 2)) := by unfold gaussJ; positivity
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs3 : 0 ≤ Real.sqrt (π / lineA c T) := Real.sqrt_nonneg _
  have hex := Real.exp_pos (1 / (6 * (T - 0.8)))
  have hex4 := Real.exp_pos (lineB c T ^ 2 / (4 * lineA c T))
  have hex5 := Real.exp_pos (lineB c T ^ 2 / (3 * lineA c T))
  have h23 : 0 ≤ 2 / Real.sqrt 3 := by positivity
  calc Real.exp (1 / (6 * (T - 0.8))) * (Real.sqrt 2 * Real.sqrt (π / lineA c T)) *
        (Real.exp (lineB c T ^ 2 / (4 * lineA c T)) * gaussJ t σ _ _ +
          2 / Real.sqrt 3 * Real.exp (lineB c T ^ 2 / (3 * lineA c T)) * gaussJ t σ _ _)
      ≤ 1.0018 * (1.41422 * 1.1053) * (1.6975 * 1.548 + 1.1548 * 2.025 * 1.1112) := by
        have hJ1' := mul_le_mul e4 hJ1 hJ1n (by norm_num)
        have hJ2' := mul_le_mul (mul_le_mul e6 e5 hex5.le (by norm_num)) hJ2 hJ2n (by norm_num)
        have hpre := mul_le_mul e1 (mul_le_mul e2 e3 hs3 (by norm_num)) (by positivity)
          (by norm_num)
        exact mul_le_mul hpre (add_le_add hJ1' hJ2') (by positivity) (by norm_num)
    _ ≤ 8.2 := by norm_num

end DeBruijnNewman
