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

/-- A uniform bound on `gaussJ t σ α β` for `t ≤ 1/2`, `0 ≤ σ ≤ 1`, `|α| ≤ αmax` and
`0 ≤ β ≤ βmax < 2`. -/
theorem gaussJ_le {t σ α β αmax βmax : ℝ} (ht : t ≤ 1 / 2) (hσ0 : 0 ≤ σ)
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

/-- `tailIntegral t T c σ ≤ 8.25` on the region, given the geometric inputs on the line through
`c`: `lineA c T ≥ 2.572`, `lineB c T² ≤ 5.45`, `c ≥ 3.739` and `|Re α(iT) - log c| ≤ 0.067`. -/
theorem tailIntegral_le {t T c σ : ℝ} (ht : t ≤ 1 / 2) (hT : 100 ≤ T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hA : 2.572 ≤ lineA c T) (hB : lineB c T ^ 2 ≤ 5.45)
    (hc : 3.739 ≤ c) (hα : |(alpha ((T : ℂ) * I)).re - Real.log c| ≤ 0.067) :
    tailIntegral t T c σ ≤ 8.25 := by
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
  have e4 : Real.exp (lineB c T ^ 2 / (4 * lineA c T)) ≤ 1.6987 := by
    refine exp_le_of_le (b := 0.5298) ?_ (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e5 : Real.exp (lineB c T ^ 2 / (3 * lineA c T)) ≤ 2.0268 := by
    refine exp_le_of_le (b := 0.7064) ?_ (by norm_num) (by norm_num)
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
  have hα1 : |(alpha ((T : ℂ) * I)).re - Real.log c + Real.log 2 / 2| ≤ 0.4136 := by
    have hl2 := Real.log_two_lt_d9
    have hl2' := Real.log_two_gt_d9
    rw [abs_le] at hα ⊢; constructor <;> linarith
  have J1 := gaussJ_le (αmax := 0.4136) (βmax := 0.00258) ht hσ0 hσ1 hβ1' hβ1 hα1
    (by norm_num)
  have J1' : Real.exp (0.4136 + 0.00258 + (0.4136 + 2 * 0.00258) ^ 2 / (8 * (1 - 0.00258 / 2))) /
      Real.sqrt (1 - 0.00258 / 2) ≤ 1.5511 := by
    have h1 : Real.exp (0.4136 + 0.00258 + (0.4136 + 2 * 0.00258) ^ 2 /
        (8 * (1 - 0.00258 / 2))) ≤ 1.55 :=
      exp_le_of_le (b := 0.4382) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ])
    have h2 : (0.99935 : ℝ) ≤ Real.sqrt (1 - 0.00258 / 2) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [div_le_iff₀ (by positivity)]; linarith
  have hβ2' : 0 ≤ 1 / (4 * T - 12) + 1 / (lineA c T * c ^ 2) := by
    have : 0 ≤ 1 / (lineA c T * c ^ 2) := by positivity
    linarith
  have J2 := gaussJ_le (αmax := 0.067) (βmax := 0.0305)
    (β := 1 / (4 * T - 12) + 1 / (lineA c T * c ^ 2)) ht hσ0 hσ1 hβ2' (by linarith) hα
    (by norm_num)
  have J2' : Real.exp (0.067 + 0.0305 + (0.067 + 2 * 0.0305) ^ 2 / (8 * (1 - 0.0305 / 2))) /
      Real.sqrt (1 - 0.0305 / 2) ≤ 1.1134 := by
    have h1 : Real.exp (0.067 + 0.0305 + (0.067 + 2 * 0.0305) ^ 2 /
        (8 * (1 - 0.0305 / 2))) ≤ 1.1048 :=
      exp_le_of_le (b := 0.0996) (by norm_num) (by norm_num) (by norm_num)
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
      ≤ 1.0018 * (1.41422 * 1.1053) * (1.6987 * 1.5511 + 1.1548 * 2.0268 * 1.1134) := by
        have hJ1' := mul_le_mul e4 hJ1 hJ1n (by norm_num)
        have hJ2' := mul_le_mul (mul_le_mul e6 e5 hex5.le (by norm_num)) hJ2 hJ2n (by norm_num)
        have hpre := mul_le_mul e1 (mul_le_mul e2 e3 hs3 (by norm_num)) (by positivity)
          (by norm_num)
        exact mul_le_mul hpre (add_le_add hJ1' hJ2') (by positivity) (by norm_num)
    _ ≤ 8.25 := by norm_num


/-! ### The line through the saddle -/

/-- The point of `[N + 1/4, N + 3/4]` nearest to `a`. -/
@[expose] noncomputable def clampC (N : ℕ) (a : ℝ) : ℝ := max (N + 1 / 4) (min (N + 3 / 4) a)

theorem clampC_ge (N : ℕ) (a : ℝ) : (N : ℝ) + 1 / 4 ≤ clampC N a := le_max_left _ _

theorem clampC_le (N : ℕ) (a : ℝ) : clampC N a ≤ N + 3 / 4 :=
  max_le (by linarith) (min_le_left _ _)

theorem clampC_le_add {N : ℕ} {a : ℝ} (ha : (N : ℝ) - 0.004 ≤ a) : clampC N a ≤ a + 0.254 :=
  max_le (by linarith) ((min_le_right _ _).trans (by linarith))

theorem sub_le_clampC {N : ℕ} {a : ℝ} (ha : a < N + 1) : a - 1 / 4 ≤ clampC N a :=
  le_max_of_le_right (le_min (by linarith) (by linarith))

/-- The geometric inputs of `tailIntegral_le` on the region: with `a = √(x/(4π))`,
`N = cutoff t x`, `c = clampC N a` and `T = x/2`. -/
theorem line_params {t x : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hx : 200 ≤ x) :
    let a := Real.sqrt (x / (4 * π))
    let c := clampC (cutoff t x) a
    (cutoff t x : ℝ) + 1 / 4 ≤ c ∧ c ≤ cutoff t x + 3 / 4 ∧ 3.739 ≤ c ∧
      2.572 ≤ lineA c (x / 2) ∧ lineB c (x / 2) ^ 2 ≤ 5.45 ∧
      |(alpha (((x / 2 : ℝ) : ℂ) * I)).re - Real.log c| ≤ 0.067 := by
  intro a c
  have hpi := Real.pi_lt_d4
  have hpi' := Real.pi_gt_d4
  have hx0 : 0 < x := by linarith
  have ha2 : a ^ 2 = x / (4 * π) := Real.sq_sqrt (by positivity)
  have ha0 : 3.989 ≤ a := by
    rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  have haN : a < cutoff t x + 1 := by
    refine lt_of_le_of_lt ?_ (sqrt_lt_cutoff_add_one t x)
    exact Real.sqrt_le_sqrt (by linarith [show 0 ≤ t / 16 by positivity])
  have hNa : (cutoff t x : ℝ) ≤ a + 0.004 := by
    refine (cutoff_le_sqrt t x).trans ?_
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc1 : (cutoff t x : ℝ) + 1 / 4 ≤ c := clampC_ge _ _
  have hc2 : c ≤ cutoff t x + 3 / 4 := clampC_le _ _
  have hca : c ≤ a + 0.254 := clampC_le_add (by linarith)
  have hac : a - 1 / 4 ≤ c := sub_le_clampC haN
  have hc0 : 3.739 ≤ c := by linarith
  have hcpos : 0 < c := by linarith
  refine ⟨hc1, hc2, hc0, ?_, ?_, ?_⟩
  · -- `lineA c T = π - a²/(2c²)`
    have e : lineA c (x / 2) = π - a ^ 2 / (2 * c ^ 2) := by
      unfold lineA; rw [ha2]; field_simp
    rw [e]
    have h1 : a ^ 2 / (2 * c ^ 2) ≤ 0.5695 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · -- `lineB c T = √2 π (c² - a²) / c`
    have e : lineB c (x / 2) = Real.sqrt 2 * π * ((c - a) * (c + a)) / c := by
      unfold lineB; rw [show x / 2 = 2 * π * a ^ 2 by rw [ha2]; field_simp; ring]
      field_simp; ring
    rw [e, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
      div_le_iff₀ (by positivity)]
    have h1 : (c - a) ^ 2 ≤ 0.254 ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h2 : (c + a) ^ 2 ≤ (2.0669 * c) ^ 2 := by
      apply sq_le_sq' (by linarith) (by nlinarith)
    have h3 : π ^ 2 ≤ 3.1416 ^ 2 := by nlinarith
    calc 2 * π ^ 2 * ((c - a) ^ 2 * (c + a) ^ 2)
        ≤ 2 * 3.1416 ^ 2 * (0.254 ^ 2 * (2.0669 * c) ^ 2) := by gcongr
      _ = 2 * 3.1416 ^ 2 * 0.254 ^ 2 * 2.0669 ^ 2 * c ^ 2 := by ring
      _ ≤ 5.45 * c ^ 2 := by nlinarith
  · -- `Re α(iT) - log c = log (a / c) - 1/(1 + T²)`
    have hT0 : 0 < x / 2 := by positivity
    rw [re_alpha_axis hT0]
    have e : 1 / 2 * Real.log (x / 2 / (2 * π)) = Real.log a := by
      rw [show x / 2 / (2 * π) = a ^ 2 by rw [ha2]; field_simp; ring, Real.log_pow]
      push_cast; ring
    rw [e]
    have hla : Real.log a - Real.log c = Real.log (a / c) := (Real.log_div (by linarith) (by linarith)).symm
    have hup : Real.log (a / c) ≤ 0.067 := by
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      rw [div_sub_one hcpos.ne', div_le_iff₀ hcpos]; linarith
    have hlo : -0.064 ≤ Real.log (a / c) := by
      have := Real.log_le_sub_one_of_pos (show 0 < c / a by positivity)
      rw [Real.log_div (by linarith) (by linarith)] at this
      rw [Real.log_div (by linarith) (by linarith)]
      have : c / a - 1 ≤ 0.064 := by
        rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]; linarith
      linarith
    have hinv : 1 / (1 + (x / 2) ^ 2) ≤ 0.0001 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hinv' : 0 ≤ 1 / (1 + (x / 2) ^ 2) := by positivity
    rw [abs_le]; constructor <;> linarith

theorem tailIntegral_nonneg (t T c σ : ℝ) : 0 ≤ tailIntegral t T c σ := by
  unfold tailIntegral gaussJ
  have := Real.sqrt_nonneg (π / lineA c T)
  positivity

/-! ### The tail estimate -/

/-- The tail of the Riemann–Siegel expansion of `H t (x + iy)` on the region is at most
`20 exp (tπ²/64) ‖M₀(i(x/2 + πt/8))‖ (1 + ε~(s₋) + ε~(conj s₊))`. -/
theorem tailEstimateWith : TailEstimateWith 20 := by
  intro t x y hr
  obtain ⟨ht0, ht, hy0, hy1, hx⟩ := hr
  obtain ⟨hc1, hc2, hc0, hA, hB, hα⟩ := line_params ht0 ht hx
  set a := Real.sqrt (x / (4 * π))
  set c := clampC (cutoff t x) a
  set N := cutoff t x
  have hT : 3 < x / 2 := by linarith
  have hT100 : 100 ≤ x / 2 := by linarith
  have hA0 : 0 < lineA c (x / 2) := by linarith
  have hβ : (1 / (4 * (x / 2) - 12) + 1 / (lineA c (x / 2) * c ^ 2)) * t < 1 := by
    have h1 : 1 / (4 * (x / 2) - 12) ≤ 0.00258 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have h2 : 1 / (lineA c (x / 2) * c ^ 2) ≤ 0.0279 := by
      rw [div_le_iff₀ (mul_pos hA0 (pow_pos (by linarith) 2))]
      have h1 : (3.739 : ℝ) ^ 2 ≤ c ^ 2 := by gcongr
      have h2 : (2.572 : ℝ) * 3.739 ^ 2 ≤ lineA c (x / 2) * c ^ 2 := by gcongr
      linarith
    have h3 : 0 ≤ 1 / (4 * (x / 2) - 12) := one_div_nonneg.2 (by linarith)
    have h4 : 0 ≤ 1 / (lineA c (x / 2) * c ^ 2) := by positivity
    nlinarith
  have key := norm_tail_le (c := c) (N := N) ht0 hT hc1 hc2 hA0 hβ y
  have hI1 := tailIntegral_le (σ := (1 - y) / 2) ht hT100 (by linarith) (by linarith) hA hB
    hc0 hα
  have hI2 := tailIntegral_le (σ := (1 + y) / 2) ht hT100 (by linarith) (by linarith) hA hB
    hc0 hα
  have hM := norm_M₀_axis_le_shift (T := x / 2) ht0 ht hT100
  have hε1 := epsTilde_nonneg (s := sMinus x y) ht0 (by rw [im_sMinus]; linarith)
  have hε2 := epsTilde_nonneg (s := (starRingEnd ℂ) (sPlus x y)) ht0
    (by rw [im_conj_sPlus]; linarith)
  have hM0 : 0 ≤ ‖M₀ (((x / 2 : ℝ) : ℂ) * I)‖ := norm_nonneg _
  have hM0' : 0 ≤ Real.exp (t * π ^ 2 / 64) * ‖M₀ (((x / 2 + π * t / 8 : ℝ) : ℂ) * I)‖ := by
    positivity
  calc _ ≤ ‖M₀ (((x / 2 : ℝ) : ℂ) * I)‖ *
        (tailIntegral t (x / 2) c ((1 - y) / 2) + tailIntegral t (x / 2) c ((1 + y) / 2)) := key
    _ ≤ (Real.exp (t * π ^ 2 / 64) * ‖M₀ (((x / 2 + π * t / 8 : ℝ) : ℂ) * I)‖ * 1.081) *
        (8.25 + 8.25) := mul_le_mul hM (add_le_add hI1 hI2)
          (add_nonneg (tailIntegral_nonneg _ _ _ _) (tailIntegral_nonneg _ _ _ _))
          (by positivity)
    _ ≤ 20 * (Real.exp (t * π ^ 2 / 64) * ‖M₀ (((x / 2 + π * t / 8 : ℝ) : ℂ) * I)‖ * 1) := by
        nlinarith
    _ ≤ _ := by gcongr; linarith

/-- Polymath Theorem 1.3 with the tail constant `20`: on the region `0 ≤ t ≤ 1/2`, `0 ≤ y ≤ 1`,
`x ≥ 200`, `‖H_t(x+iy) - B_t(x+iy) f_t(x+iy)‖ ≤ ‖B_t(x+iy)‖ (errAB + 20 errC0)`. -/
theorem effectiveApproximationWith : EffectiveApproximationWith 20 :=
  effectiveApproximation_of_tail (by norm_num) tailEstimateWith

/-- The nonvanishing test, unconditionally: on the region, if
`errABExplicit t x y + 20 errC0 t x y < ‖f t x y‖` then `H t (x + iy) ≠ 0`. -/
theorem H_ne_zero_of_lt_norm_f'' {t x y : ℝ} (hr : InRegion t x y)
    (hf : errABExplicit t x y + 20 * errC0 t x y < ‖f t x y‖) : H t (x + y * I) ≠ 0 :=
  H_ne_zero_of_lt_norm_f' effectiveApproximationWith hr hf

end DeBruijnNewman
