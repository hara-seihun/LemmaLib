/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.Analysis.Complex.ContourShift
public import LemmaLib.Analysis.SpecialFunctions.Gamma.Stirling
public import LemmaLib.NumberTheory.DeBruijnNewman.AlphaBounds
public import LemmaLib.NumberTheory.DeBruijnNewman.RiemannSiegel

/-!
# The heat flow of the Riemann–Siegel main terms

This file proves Polymath Proposition 6.1 (*Effective approximation of heat flow evolution of the
Riemann ξ function*, Res. Math. Sci. 6 (2019)): for `0 ≤ t ≤ 1/2`, `n ≥ 1` and `Im s > 10`,

`r_{t,n}(s) = M_t(s) b_n^t n^{-s - (t/2) α(s)} (1 + O_≤(ε_{t,n}(s)))`

with `ε_{t,n}(σ + iT) = exp ((t²/8 |α(σ+iT) - log n|² + t/4 + 1/6) / (T - 3.33)) - 1`
(`rtnEstimate : RtnEstimate`).

The proof follows Polymath. Stirling's formula with an explicit remainder
(`LemmaLib.Analysis.SpecialFunctions.Gamma.Stirling`) gives
`r₀ n w = M₀ w n^{-w} exp E` with `‖E‖ ≤ 1/(6 (Im w - 0.8))` (`exists_r₀_eq`). The Gaussian
integral defining `r t n s = ∫ r₀ n (s + √t v) e^{-v²}/√π dv` is shifted to the line
`Im v = Im c`, `c = (√t/2)(α(s) - log n)` (`Complex.integral_add_eq_integral`, using the Gaussian
decay `exists_strip_bound` of the integrand on the strip), after which the second-order Taylor
expansion of `log M₀` around `s` (`shifted_integrand`, `exists_shifted_eq`) writes the integrand
as `mainTerm t n s * exp δ * gauss u` with `‖δ‖ ≤ κ u² + A`, and
`∫ (exp (κ u² + A) - 1) gauss u = exp A / √(1 - κ) - 1 ≤ ε_{t,n}(s)` (`integral_exp_mul_gauss`,
`inv_sqrt_le_exp`).
-/

public section

open Complex Real Set Filter Topology MeasureTheory intervalIntegral

namespace DeBruijnNewman

/-- `n^{-w} = exp (-(w log n))` for `n ≥ 1`. -/
theorem natCast_cpow_neg_eq_exp {n : ℕ} (hn : 1 ≤ n) (w : ℂ) :
    (n : ℂ) ^ (-w) = Complex.exp (-(w * Real.log n)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.natCast_log]
  ring_nf

/-- Stirling's formula for `r₀`: for `Im w > 0.8`, `r₀ n w = M₀ w n^{-w} exp E` with
`‖E‖ ≤ 1 / (6 (Im w - 0.8))`. -/
theorem exists_r₀_eq (n : ℕ) {w : ℂ} (hw : 0.8 < w.im) :
    ∃ E : ℂ, ‖E‖ ≤ 1 / (6 * (w.im - 0.8)) ∧
      r₀ n w = M₀ w * (n : ℂ) ^ (-w) * Complex.exp E := by
  have hz : (w / 2).im ≠ 0 := by
    rw [Complex.div_ofNat_im]; intro h; linarith
  obtain ⟨E, hE, hΓ⟩ := Complex.Stirling.exists_Gamma_eq_sqrt_two_pi_mul_exp hz
  refine ⟨E, ?_, ?_⟩
  · refine hE.trans ?_
    rw [Complex.div_ofNat_im, norm_div, Complex.norm_ofNat]
    have hT : 0 < w.im := by linarith
    have hnorm : w.im ≤ ‖w‖ := (le_abs_self _).trans (Complex.abs_im_le_norm w)
    have hw0 : 0 < ‖w‖ := by linarith
    have h1 : 1 / (12 * (‖w‖ / 2)) ≤ 1 / (6 * w.im) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : 1 / (30 * (w.im / 2) ^ 2) = 2 / (15 * w.im ^ 2) := by
      field_simp
      ring
    rw [h2]
    have h3 : 1 / (6 * w.im) + 2 / (15 * w.im ^ 2) ≤ 1 / (6 * (w.im - 0.8)) := by
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    linarith
  · rw [r₀, M₀, hΓ]
    have : (w / 2 - 1 / 2) * Complex.log (w / 2) - w / 2 + E =
        ((w / 2 - 1 / 2) * Complex.log (w / 2) - w / 2) + E := by ring
    rw [this, Complex.exp_add]
    ring

/-- `‖α(ζ)‖ ≤ 5 + ‖ζ‖ / 2` for `Im ζ ≥ 1`. -/
theorem norm_alpha_le_of_one_le_im {ζ : ℂ} (hζ : 1 ≤ ζ.im) : ‖alpha ζ‖ ≤ 5 + ‖ζ‖ / 2 := by
  have hζ0 : ζ ≠ 0 := fun h => by rw [h] at hζ; norm_num at hζ
  have hζ1 : ζ - 1 ≠ 0 := fun h => by
    have : ζ = 1 := sub_eq_zero.1 h
    rw [this] at hζ; norm_num at hζ
  have hnorm : 1 ≤ ‖ζ‖ := hζ.trans ((le_abs_self _).trans (Complex.abs_im_le_norm ζ))
  have hnorm1 : 1 ≤ ‖ζ - 1‖ := by
    have : (ζ - 1).im = ζ.im := by simp
    exact (hζ.trans_eq this.symm).trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  unfold alpha
  refine (norm_add₃_le).trans ?_
  have h1 : ‖1 / (2 * ζ)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have h2 : ‖1 / (ζ - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]
    exact hnorm1
  have h3 : ‖1 / 2 * Complex.log (ζ / (2 * π))‖ ≤ (‖ζ‖ + Real.log (2 * π) + π) / 2 := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_ofNat, one_div, mul_comm, ← div_eq_mul_inv]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im, norm_div, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Real.log_div (by positivity) (by positivity)]
    have hl : 0 ≤ Real.log ‖ζ‖ := Real.log_nonneg hnorm
    have hl2 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hlz : Real.log ‖ζ‖ ≤ ‖ζ‖ := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < ‖ζ‖)]
    have harg := Complex.abs_arg_le_pi (ζ / (2 * π))
    calc |Real.log ‖ζ‖ - Real.log (2 * π)| + |(ζ / (2 * π)).arg|
        ≤ (Real.log ‖ζ‖ + Real.log (2 * π)) + π := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ ≤ ‖ζ‖ + Real.log (2 * π) + π := by linarith
  have hlog : Real.log (2 * π) ≤ 2 := by
    have h8 : (2 * π) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      have h4 : Real.exp 1 ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_one_gt_d9, Real.pi_lt_d2, Real.exp_pos 1]
    calc Real.log (2 * π) ≤ Real.log (Real.exp 2) :=
          Real.log_le_log (by positivity) h8
      _ = 2 := Real.log_exp 2
  linarith [Real.pi_lt_four]

/-- `Im α(s) ≥ -3/(2 Im s)` for `Im s > 0`. -/
theorem im_alpha_ge {s : ℂ} (hs : 0 < s.im) : -(3 / (2 * s.im)) ≤ (alpha s).im := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1 : s - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  have hN : 0 < Complex.normSq s := Complex.normSq_pos.2 hs0
  have hN1 : 0 < Complex.normSq (s - 1) := Complex.normSq_pos.2 hs1
  have him : s.im * s.im ≤ Complex.normSq s := Complex.im_sq_le_normSq s
  have him1 : s.im * s.im ≤ Complex.normSq (s - 1) := by
    have := Complex.im_sq_le_normSq (s - 1)
    simpa using this
  have h3 : 0 ≤ (1 / 2 * Complex.log (s / (2 * π))).im := by
    rw [Complex.mul_im, Complex.log_im]
    simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
    have : 0 ≤ (s / (2 * π)).arg := Complex.arg_nonneg_iff.2 (by
      rw [Complex.div_im]
      simp
      positivity)
    simp only [zero_div, zero_mul, add_zero]
    positivity
  have h1 : -(1 / (2 * s.im)) ≤ (1 / (2 * s)).im := by
    rw [Complex.div_im]
    simp
    rw [div_le_iff₀ (by positivity)]
    have : s.im⁻¹ * 2⁻¹ * (2 * 2 * normSq s) = 2 * normSq s / s.im := by field_simp
    rw [this, le_div_iff₀ hs]
    nlinarith
  have h2 : -(1 / s.im) ≤ (1 / (s - 1)).im := by
    rw [Complex.div_im]
    simp
    rw [div_le_iff₀ (by positivity)]
    have : s.im⁻¹ * normSq (s - 1) = normSq (s - 1) / s.im := by field_simp
    rw [this, le_div_iff₀ hs]
    nlinarith
  unfold alpha
  rw [Complex.add_im, Complex.add_im]
  have : -(3 / (2 * s.im)) = -(1 / (2 * s.im)) + -(1 / s.im) + 0 := by
    field_simp; ring
  rw [this]
  exact add_le_add (add_le_add h1 h2) h3

/-- `‖exp x - 1‖ ≤ exp ‖x‖ - 1`. -/
theorem norm_exp_sub_one_le_exp_norm_sub_one (x : ℂ) : ‖Complex.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum x 1
  simpa using this

/-- `mainTerm t n s = exp (log M₀(s) - s log n + (t/4) (α(s) - log n)²)`. -/
theorem mainTerm_eq_exp (t : ℝ) {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : s.im ≠ 0) :
    mainTerm t n s =
      Complex.exp (logM₀ s - s * Real.log n + t / 4 * (alpha s - Real.log n) ^ 2) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [mainTerm, M, M₀_eq_exp_logM₀ (ne_zero_of_im_ne_zero hs) (ne_one_of_im_ne_zero hs), b,
    Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- The shifted integrand of `r t n s`: with `h = √t u + (t/2)(α(s) - log n)`,
`r₀ n (s + h) exp (-√t u (α(s) - log n) - (t/4)(α(s) - log n)²) = mainTerm t n s exp (ρ + E)`
where `ρ` is the second-order Taylor remainder of `log M₀` and `E` the Stirling error. -/
theorem shifted_integrand {t : ℝ} {n : ℕ} {s : ℂ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hn : 1 ≤ n)
    (hs : 10 < s.im) (u : ℝ) :
    ∃ ρ E : ℂ,
      ‖ρ‖ ≤ ‖(Real.sqrt t : ℂ) * u + t / 2 * (alpha s - Real.log n)‖ ^ 2 / (4 * (s.im - 3.08)) ∧
      ‖E‖ ≤ 1 / (6 * (s.im - 3.33)) ∧
      r₀ n (s + (Real.sqrt t * u + t / 2 * (alpha s - Real.log n))) *
        Complex.exp (-(Real.sqrt t * u * (alpha s - Real.log n)) -
          t / 4 * (alpha s - Real.log n) ^ 2) =
        mainTerm t n s * Complex.exp (ρ + E) := by
  set αn : ℂ := alpha s - Real.log n with hαn
  set h : ℂ := (Real.sqrt t : ℂ) * u + t / 2 * αn with hh
  have hT : 0 < s.im := by linarith
  have him_αn : -(3 / (2 * s.im)) ≤ αn.im := by
    rw [hαn, Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact im_alpha_ge hT
  have him_h : -0.0375 ≤ h.im := by
    rw [hh, Complex.add_im, Complex.mul_im, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add,
      Complex.div_ofNat_re, Complex.div_ofNat_im]
    have h1 : t / 2 * αn.im ≥ t / 2 * (-(3 / (2 * s.im))) :=
      mul_le_mul_of_nonneg_left him_αn (by positivity)
    have h2 : t / 2 * (-(3 / (2 * s.im))) ≥ -0.0375 := by
      rw [mul_neg, ge_iff_le, neg_le_neg_iff, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, s.im - 0.0375 ≤ (s + τ * h).im := by
    intro τ hτ
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    nlinarith [hτ.1, hτ.2]
  -- Stirling
  have hw : 0.8 < (s + h).im := by
    have := hseg 1 (right_mem_Icc.2 zero_le_one)
    simp only [Complex.ofReal_one, one_mul] at this
    linarith
  obtain ⟨E, hE, hr₀⟩ := exists_r₀_eq n hw
  -- Taylor
  set K : ℝ := 1 / (2 * (s.im - 3.08)) with hK
  have hg : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt logM₀ (alpha (s + τ * h)) (s + τ * h) := fun τ hτ =>
    hasDerivAt_logM₀ (by linarith [hseg τ hτ])
  have hg' : ∀ τ ∈ Icc (0 : ℝ) 1, ‖alpha (s + τ * h) - alpha s‖ ≤ K * (τ * ‖h‖) := by
    have := norm_sub_le_of_hasDerivAt_segment (g := alpha) (g' := alpha') (z := s) (h := h) (K := K)
      (fun τ hτ => hasDerivAt_alpha (by linarith [hseg τ hτ])) (fun τ hτ => ?_)
    · intro τ hτ
      have := this τ hτ
      linarith [this, mul_comm τ ‖h‖]
    · refine (norm_alpha'_le (by linarith [hseg τ hτ])).trans ?_
      rw [hK]
      exact one_div_le_one_div_of_le (by linarith) (by linarith [hseg τ hτ])
  have htaylor := norm_taylor_two_le hg hg'
  refine ⟨logM₀ (s + h) - logM₀ s - h * alpha s, E, ?_, ?_, ?_⟩
  · refine htaylor.trans (le_of_eq ?_)
    rw [hK]; field_simp; ring
  · refine hE.trans ?_
    have := hseg 1 (right_mem_Icc.2 zero_le_one)
    simp only [Complex.ofReal_one, one_mul] at this
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · have hs0 : s ≠ 0 := ne_zero_of_im_ne_zero hT.ne'
    have hw0 : s + h ≠ 0 := ne_zero_of_im_ne_zero (by linarith)
    have hw1 : s + h ≠ 1 := ne_one_of_im_ne_zero (by linarith)
    rw [hr₀, M₀_eq_exp_logM₀ hw0 hw1, natCast_cpow_neg_eq_exp hn, mainTerm_eq_exp t hn hT.ne',
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hh, hαn]
    ring

/-! ### Growth of the integrand on a horizontal strip -/

/-- `r₀ n` is differentiable away from the real axis. -/
theorem differentiableAt_r₀ {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : w.im ≠ 0) :
    DifferentiableAt ℂ (r₀ n) w := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓ : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) w := by
    refine (Complex.differentiableAt_Gamma (w / 2) fun m h => hw ?_).comp w (by fun_prop)
    have := congrArg Complex.im h
    simpa using this
  unfold r₀
  refine (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s * (s - 1) / 16) w).mul
    (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hπ))).mul hΓ).mul
    (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hn0))

/-- `‖r₀ n w‖ ≤ exp (‖log M₀ w‖ + |Re w| log n + 1)` for `Im w ≥ 9`. -/
theorem norm_r₀_le {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 9 ≤ w.im) :
    ‖r₀ n w‖ ≤ Real.exp (‖logM₀ w‖ + |w.re| * Real.log n + 1) := by
  obtain ⟨E, hE, hr⟩ := exists_r₀_eq n (by linarith : 0.8 < w.im)
  have hw0 : w ≠ 0 := ne_zero_of_im_ne_zero (by linarith)
  have hw1 : w ≠ 1 := ne_one_of_im_ne_zero (by linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [hr, norm_mul, norm_mul, norm_M₀ hw0 hw1, Complex.norm_natCast_cpow_of_pos (by omega),
    Complex.norm_exp, Real.rpow_def_of_pos hn0, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : (logM₀ w).re ≤ ‖logM₀ w‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have h2 : Real.log n * (-w).re ≤ |w.re| * Real.log n := by
    rw [Complex.neg_re, mul_neg, mul_comm]
    exact (neg_le_abs _).trans (le_of_eq (by rw [abs_mul, abs_of_nonneg hlog]))
  have h3 : E.re ≤ 1 := by
    refine ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans (hE.trans ?_)
    rw [div_le_one (by linarith)]
    linarith
  linarith

/-- Growth of `log M₀` along a horizontal segment: for `Im z₀ ≥ 1`, `0 ≤ σ ≤ 1` and real `x`,
`‖log M₀ (z₀ + σ x)‖ ≤ ‖log M₀ z₀‖ + (5 + (‖z₀‖ + |x|) / 2) |x|`. -/
theorem norm_logM₀_add_le {z₀ : ℂ} (hz₀ : 1 ≤ z₀.im) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (x : ℝ) :
    ‖logM₀ (z₀ + σ * x)‖ ≤ ‖logM₀ z₀‖ + (5 + (‖z₀‖ + |x|) / 2) * |x| := by
  have him : ∀ τ ∈ Icc (0 : ℝ) 1, (z₀ + τ * ((σ * x : ℝ) : ℂ)).im = z₀.im := by
    intro τ _
    simp
  have hnorm : ∀ τ ∈ Icc (0 : ℝ) 1, ‖z₀ + τ * ((σ * x : ℝ) : ℂ)‖ ≤ ‖z₀‖ + |x| := by
    intro τ hτ
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hτ.1, abs_mul, abs_of_nonneg hσ0]
    have : τ * (σ * |x|) ≤ |x| := by
      calc τ * (σ * |x|) ≤ 1 * (1 * |x|) := by gcongr; exact hτ.2
        _ = |x| := by ring
    linarith
  have key := norm_sub_le_of_hasDerivAt_segment (g := logM₀) (g' := alpha) (z := z₀)
    (h := ((σ * x : ℝ) : ℂ)) (K := 5 + (‖z₀‖ + |x|) / 2)
    (fun τ hτ => hasDerivAt_logM₀ (by rw [him τ hτ]; linarith))
    (fun τ hτ => by
      refine (norm_alpha_le_of_one_le_im (by rw [him τ hτ]; exact hz₀)).trans ?_
      linarith [hnorm τ hτ]) 1 (right_mem_Icc.2 zero_le_one)
  simp only [Complex.ofReal_one, one_mul, mul_one, Complex.ofReal_mul] at key
  have : ‖logM₀ (z₀ + σ * x)‖ ≤ ‖logM₀ z₀‖ + ‖logM₀ (z₀ + σ * x) - logM₀ z₀‖ := by
    have := norm_add_le (logM₀ z₀) (logM₀ (z₀ + σ * x) - logM₀ z₀)
    simpa using this
  refine this.trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hσ0] at key
  have : (5 + (‖z₀‖ + |x|) / 2) * (σ * |x|) ≤ (5 + (‖z₀‖ + |x|) / 2) * |x| := by
    have : σ * |x| ≤ |x| := by
      calc σ * |x| ≤ 1 * |x| := by gcongr
        _ = |x| := one_mul _
    exact mul_le_mul_of_nonneg_left this (by positivity)
  linarith

/-- Gaussian decay of the integrand `v ↦ r₀ n (s + √t v) e^{-v²}/√π` on a horizontal strip
`Im v ∈ [0, β]` (or `[β, 0]`) of width at most `1`. -/
theorem exists_strip_bound {t : ℝ} {n : ℕ} {s : ℂ} (ht : t ≤ 1 / 2) (hn : 1 ≤ n)
    (hs : 10 < s.im) {β : ℝ} (hβ : |β| ≤ 1) :
    ∃ C : ℝ, ∀ v : ℂ, v.im ∈ uIcc 0 β →
      ‖r₀ n (s + Real.sqrt t * v) * (Complex.exp (-v ^ 2) / (Real.sqrt π : ℂ))‖ ≤
        C * Real.exp (-(1 / 4) * v.re ^ 2) := by
  have hst0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hst1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hy1 : ∀ y ∈ uIcc (0 : ℝ) β, |y| ≤ 1 := fun y hy => by
    have := abs_sub_left_of_mem_uIcc hy
    simp only [sub_zero] at this
    linarith
  have him : ∀ y ∈ uIcc (0 : ℝ) β, 9 ≤ (s + Real.sqrt t * (y * I)).im := fun y hy => by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_mul]
    have h1 := hy1 y hy
    have : Real.sqrt t * y ≥ -1 := by
      have : Real.sqrt t * |y| ≤ 1 := by
        calc Real.sqrt t * |y| ≤ 1 * 1 := by gcongr
          _ = 1 := one_mul 1
      have := neg_abs_le y
      nlinarith
    linarith
  obtain ⟨K₀, hK₀⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := β)).exists_bound_of_continuousOn
    (f := fun y : ℝ => logM₀ (s + Real.sqrt t * (y * I))) (fun y hy =>
      ((hasDerivAt_logM₀ (by linarith [him y hy])).continuousAt.comp
        (f := fun y : ℝ => s + Real.sqrt t * (y * I)) (by fun_prop)).continuousWithinAt)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  set A₁ : ℝ := 5 + (‖s‖ + 1) / 2 with hA₁
  refine ⟨Real.exp (K₀ + 2 + ‖s‖ * Real.log n + (A₁ + Real.log n) ^ 2) / Real.sqrt π, ?_⟩
  intro v hv
  have hv_eq : v = (v.re : ℂ) + (v.im : ℂ) * I := (Complex.re_add_im v).symm
  set x := v.re with hx
  set y := v.im with hy
  set z₀ : ℂ := s + Real.sqrt t * (y * I) with hz₀
  have hw_eq : s + Real.sqrt t * v = z₀ + Real.sqrt t * x := by rw [hv_eq, hz₀]; ring
  have hz₀norm : ‖z₀‖ ≤ ‖s‖ + 1 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hst0]
    have : Real.sqrt t * |y| ≤ 1 := by
      calc Real.sqrt t * |y| ≤ 1 * 1 := by gcongr; exact hy1 y hv
        _ = 1 := one_mul 1
    linarith
  have hRew : |(s + Real.sqrt t * v).re| ≤ ‖s‖ + |x| := by
    rw [hw_eq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.ofReal_re]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hst0]
    have h1 : |z₀.re| ≤ ‖z₀‖ := Complex.abs_re_le_norm z₀
    have h2 : Real.sqrt t * |x| ≤ |x| := by
      calc Real.sqrt t * |x| ≤ 1 * |x| := by gcongr
        _ = |x| := one_mul _
    have h3 : z₀.re = s.re := by rw [hz₀]; simp
    rw [h3] at h1 ⊢
    linarith [Complex.abs_re_le_norm s]
  have hr := norm_r₀_le hn (w := s + Real.sqrt t * v) (by rw [hw_eq]; simpa [hz₀] using him y hv)
  have hlogM := norm_logM₀_add_le (z₀ := z₀) (by linarith [him y hv]) hst0 hst1 x
  have hK := hK₀ y hv
  rw [norm_mul, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 Real.pi_pos)]
  have hRe : (-v ^ 2).re = -(x ^ 2 - y ^ 2) := by
    rw [hv_eq]; simp [sq]
  rw [hRe, mul_div_assoc', div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right (Real.sqrt_pos.2 Real.pi_pos)]
  have hy2 : y ^ 2 ≤ 1 := by
    have := hy1 y hv
    nlinarith [abs_nonneg y, sq_abs y]
  calc ‖r₀ n (s + Real.sqrt t * v)‖ * Real.exp (-(x ^ 2 - y ^ 2))
      ≤ Real.exp (‖logM₀ (s + Real.sqrt t * v)‖ + |(s + Real.sqrt t * v).re| * Real.log n + 1) *
        Real.exp (-(x ^ 2 - y ^ 2)) := by gcongr
    _ = Real.exp (‖logM₀ (s + Real.sqrt t * v)‖ + |(s + Real.sqrt t * v).re| * Real.log n + 1 +
        -(x ^ 2 - y ^ 2)) := by rw [← Real.exp_add]
    _ ≤ Real.exp (K₀ + 2 + ‖s‖ * Real.log n + (A₁ + Real.log n) ^ 2 + -(1 / 4) * x ^ 2) := by
        refine Real.exp_le_exp.2 ?_
        rw [← hw_eq] at hlogM
        have h5 : |(s + Real.sqrt t * v).re| * Real.log n ≤ (‖s‖ + |x|) * Real.log n :=
          mul_le_mul_of_nonneg_right hRew hlog
        have h6 : (5 + (‖z₀‖ + |x|) / 2) * |x| ≤ (A₁ + |x| / 2) * |x| := by
          rw [hA₁]
          exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg x)
        have h7 : (A₁ + Real.log n) * |x| ≤ (A₁ + Real.log n) ^ 2 + x ^ 2 / 4 := by
          nlinarith [sq_nonneg (A₁ + Real.log n - |x| / 2), sq_abs x]
        nlinarith [sq_abs x]
    _ = _ := by rw [Real.exp_add]

/-! ### Gaussian integrals -/

/-- `∫ gauss = 1`. -/
theorem integral_gauss : ∫ v : ℝ, gauss v = 1 := by
  unfold gauss
  rw [MeasureTheory.integral_div]
  have := integral_gaussian (1 : ℝ)
  simp only [one_mul, neg_mul, div_one] at this
  rw [this, div_self (Real.sqrt_pos.2 Real.pi_pos).ne']

theorem exp_mul_gauss_eq (κ A v : ℝ) :
    Real.exp (κ * v ^ 2 + A) * gauss v =
      Real.exp A / Real.sqrt π * Real.exp (-(1 - κ) * v ^ 2) := by
  unfold gauss
  have : -(1 - κ) * v ^ 2 = κ * v ^ 2 + -v ^ 2 := by ring
  rw [this, Real.exp_add, Real.exp_add]
  field_simp

theorem integrable_gauss : Integrable gauss := by
  unfold gauss
  have := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).div_const (Real.sqrt π)
  simpa using this

theorem integrable_exp_mul_gauss {κ : ℝ} (A : ℝ) (hκ : κ < 1) :
    Integrable fun v : ℝ => Real.exp (κ * v ^ 2 + A) * gauss v := by
  simp_rw [exp_mul_gauss_eq]
  exact (integrable_exp_neg_mul_sq (by linarith)).const_mul _

/-- `∫ exp (κ v² + A) gauss v = exp A / √(1 - κ)` for `κ < 1`. -/
theorem integral_exp_mul_gauss {κ A : ℝ} (hκ : κ < 1) :
    ∫ v : ℝ, Real.exp (κ * v ^ 2 + A) * gauss v = Real.exp A / Real.sqrt (1 - κ) := by
  simp_rw [exp_mul_gauss_eq]
  rw [MeasureTheory.integral_const_mul, integral_gaussian, Real.sqrt_div' _ (by linarith)]
  field_simp

/-- `1 / √(1 - t/(2(T - 3.08))) ≤ exp (t / (4 (T - 3.33)))` for `0 ≤ t ≤ 1/2`, `T > 10`. -/
theorem inv_sqrt_le_exp {t T : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hT : 10 < T) :
    1 / Real.sqrt (1 - t / (2 * (T - 3.08))) ≤ Real.exp (t / (4 * (T - 3.33))) := by
  set x := t / (2 * (T - 3.33)) with hx
  have hT1 : 0 < T - 3.33 := by linarith
  have hT2 : 0 < T - 3.08 := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hexp : Real.exp (-x) ≤ 1 - t / (2 * (T - 3.08)) := by
    have h1 : Real.exp (-x) ≤ 1 / (1 + x) := by
      rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos x) (by linarith)]
      exact Real.add_one_le_exp x |>.trans_eq' (by ring)
    refine h1.trans ?_
    rw [hx]
    have h2 : 1 / (1 + t / (2 * (T - 3.33))) = 2 * (T - 3.33) / (2 * (T - 3.33) + t) := by
      field_simp
    have h3 : 1 - t / (2 * (T - 3.08)) = (2 * (T - 3.08) - t) / (2 * (T - 3.08)) := by
      field_simp
    rw [h2, h3, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have : t / (4 * (T - 3.33)) = x / 2 := by rw [hx]; field_simp; ring
  rw [this, Real.exp_half, one_div, ← Real.sqrt_inv]
  refine Real.sqrt_le_sqrt ?_
  rw [inv_le_comm₀ (by linarith [Real.exp_pos (-x)]) (Real.exp_pos _), ← Real.exp_neg]
  exact hexp

/-- `Im α(s) ≤ π/2` for `Im s > 0`. -/
theorem im_alpha_le {s : ℂ} (hs : 0 < s.im) : (alpha s).im ≤ π / 2 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1 : s - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  have hN : 0 < Complex.normSq s := Complex.normSq_pos.2 hs0
  have hN1 : 0 < Complex.normSq (s - 1) := Complex.normSq_pos.2 hs1
  have h1 : (1 / (2 * s)).im ≤ 0 := by
    rw [Complex.div_im]
    simp
    positivity
  have h2 : (1 / (s - 1)).im ≤ 0 := by
    rw [Complex.div_im]
    simp
    positivity
  have h3 : (1 / 2 * Complex.log (s / (2 * π))).im ≤ π / 2 := by
    rw [Complex.mul_im, Complex.log_im]
    simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im,
      zero_div, zero_mul, add_zero]
    have := Complex.arg_le_pi (s / (2 * π))
    linarith
  unfold alpha
  rw [Complex.add_im, Complex.add_im]
  linarith

/-- The pointwise form of the shifted integrand: `Fc (u + c) = mainTerm t n s * exp δ * gauss u`
with `‖δ‖ ≤ κ u² + A`, where `c = (√t/2) (α(s) - log n)`, `κ = t / (2 (Im s - 3.08))` and
`A = t² ‖α(s) - log n‖² / (8 (Im s - 3.33)) + 1 / (6 (Im s - 3.33))`. -/
theorem exists_shifted_eq {t : ℝ} {n : ℕ} {s : ℂ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hn : 1 ≤ n)
    (hs : 10 < s.im) (u : ℝ) :
    ∃ δ : ℂ, ‖δ‖ ≤ t / (2 * (s.im - 3.08)) * u ^ 2 +
        (t ^ 2 * ‖alpha s - Real.log n‖ ^ 2 / (8 * (s.im - 3.33)) + 1 / (6 * (s.im - 3.33))) ∧
      r₀ n (s + Real.sqrt t * (u + Real.sqrt t / 2 * (alpha s - Real.log n))) *
        (Complex.exp (-(u + Real.sqrt t / 2 * (alpha s - Real.log n)) ^ 2) / (Real.sqrt π : ℂ)) =
      mainTerm t n s * Complex.exp δ * (gauss u : ℂ) := by
  obtain ⟨ρ, E, hρ, hE, heq⟩ := shifted_integrand ht0 ht hn hs u
  set αn : ℂ := alpha s - Real.log n with hαn
  have hst : (Real.sqrt t : ℂ) * Real.sqrt t = t := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht0]
  refine ⟨ρ + E, ?_, ?_⟩
  · refine (norm_add_le _ _).trans ?_
    have h1 : ‖(Real.sqrt t : ℂ) * u + t / 2 * αn‖ ^ 2 ≤
        2 * (t * u ^ 2 + t ^ 2 / 4 * ‖αn‖ ^ 2) := by
      have := norm_add_le ((Real.sqrt t : ℂ) * u) (t / 2 * αn)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t), norm_div, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at this
      have h2 : (Real.sqrt t * |u| + t / 2 * ‖αn‖) ^ 2 ≤
          2 * (t * u ^ 2 + t ^ 2 / 4 * ‖αn‖ ^ 2) := by
        have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
        nlinarith [sq_nonneg (Real.sqrt t * |u| - t / 2 * ‖αn‖), sq_abs u]
      calc ‖(Real.sqrt t : ℂ) * u + t / 2 * αn‖ ^ 2 ≤ (Real.sqrt t * |u| + t / 2 * ‖αn‖) ^ 2 := by
            gcongr
        _ ≤ _ := h2
    have hT1 : 0 < s.im - 3.33 := by linarith
    have hT2 : 0 < s.im - 3.08 := by linarith
    have h3 : ‖ρ‖ ≤ t / (2 * (s.im - 3.08)) * u ^ 2 + t ^ 2 * ‖αn‖ ^ 2 / (8 * (s.im - 3.33)) := by
      refine hρ.trans ?_
      calc ‖(Real.sqrt t : ℂ) * u + t / 2 * αn‖ ^ 2 / (4 * (s.im - 3.08))
          ≤ 2 * (t * u ^ 2 + t ^ 2 / 4 * ‖αn‖ ^ 2) / (4 * (s.im - 3.08)) := by gcongr
        _ = t / (2 * (s.im - 3.08)) * u ^ 2 + t ^ 2 * ‖αn‖ ^ 2 / (8 * (s.im - 3.08)) := by
            field_simp; ring
        _ ≤ _ := by
            gcongr
            linarith
    linarith
  · have hcalc : s + Real.sqrt t * (u + Real.sqrt t / 2 * αn) =
        s + (Real.sqrt t * u + t / 2 * αn) := by
      rw [← hst]; ring
    have hexp : Complex.exp (-(u + Real.sqrt t / 2 * αn) ^ 2) =
        Complex.exp (-(Real.sqrt t * u * αn) - t / 4 * αn ^ 2) * Complex.exp (-(u : ℂ) ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      rw [← hst]; ring
    rw [hcalc, hexp, gauss, Complex.ofReal_div, Complex.ofReal_exp]
    push_cast
    calc r₀ n (s + (Real.sqrt t * u + t / 2 * αn)) *
          (Complex.exp (-(Real.sqrt t * u * αn) - t / 4 * αn ^ 2) * Complex.exp (-(u : ℂ) ^ 2) /
            (Real.sqrt π : ℂ))
        = r₀ n (s + (Real.sqrt t * u + t / 2 * αn)) *
          Complex.exp (-(Real.sqrt t * u * αn) - t / 4 * αn ^ 2) *
            (Complex.exp (-(u : ℂ) ^ 2) / (Real.sqrt π : ℂ)) := by ring
      _ = _ := by rw [heq]

/-- **Polymath Proposition 6.1.** For `0 ≤ t ≤ 1/2`, `n ≥ 1` and `Im s > 10`,
`‖r t n s - mainTerm t n s‖ ≤ ‖mainTerm t n s‖ * epsR t n s`. -/
theorem rtnEstimate : RtnEstimate := by
  intro t n s ht0 ht hn hs
  have hT1 : 0 < s.im - 3.33 := by linarith
  have hT2 : 0 < s.im - 3.08 := by linarith
  set αn : ℂ := alpha s - Real.log n with hαn
  set c : ℂ := Real.sqrt t / 2 * αn with hc
  set Fc : ℂ → ℂ := fun v => r₀ n (s + Real.sqrt t * v) * (Complex.exp (-v ^ 2) / (Real.sqrt π : ℂ))
    with hFc
  have hst0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hst1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  -- `|Im c| ≤ 1`
  have hcim : |c.im| ≤ 1 := by
    rw [hc, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_div, zero_mul, add_zero]
    have h1 : αn.im = (alpha s).im := by
      rw [hαn, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [h1, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt t / 2)]
    have h2 : |(alpha s).im| ≤ 2 := by
      rw [abs_le]
      constructor
      · have := im_alpha_ge (by linarith : 0 < s.im)
        have : 3 / (2 * s.im) ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        linarith
      · linarith [im_alpha_le (by linarith : 0 < s.im), Real.pi_lt_four]
    calc Real.sqrt t / 2 * |(alpha s).im| ≤ 1 / 2 * 2 := by gcongr
      _ = 1 := by norm_num
  -- `r t n s = ∫ Fc (u + c) du`
  have hr : r t n s = ∫ u : ℝ, Fc (u + c) := by
    obtain ⟨C, hC⟩ := exists_strip_bound ht hn hs hcim
    have hshift := Complex.integral_add_eq_integral (F := Fc) (c := c) (a := 1 / 4) (C := C)
      (by norm_num) (fun v hv => ?_) hC
    · rw [r, hshift]
      congr 1
      ext u
      rw [hFc]
      simp only [gauss, Complex.ofReal_div, Complex.ofReal_exp]
      push_cast
      ring_nf
    · -- differentiability on the strip
      have him : (s + Real.sqrt t * v).im ≠ 0 := by
        rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero]
        have h1 : |v.im| ≤ 1 := by
          have := abs_sub_left_of_mem_uIcc hv
          simp only [sub_zero] at this
          linarith
        have : Real.sqrt t * |v.im| ≤ 1 := by
          calc Real.sqrt t * |v.im| ≤ 1 * 1 := by gcongr
            _ = 1 := one_mul 1
        have := neg_abs_le v.im
        nlinarith
      rw [hFc]
      refine DifferentiableAt.mul ?_ (by fun_prop)
      exact (differentiableAt_r₀ hn him).comp v (f := fun v : ℂ => s + Real.sqrt t * v)
        (by fun_prop)
  -- the pointwise bound
  set κ : ℝ := t / (2 * (s.im - 3.08)) with hκ
  set A : ℝ := t ^ 2 * ‖αn‖ ^ 2 / (8 * (s.im - 3.33)) + 1 / (6 * (s.im - 3.33)) with hA
  have hκ1 : κ < 1 := by
    rw [hκ, div_lt_one (by linarith)]; linarith
  have hpt : ∀ u : ℝ, ‖Fc (u + c) - mainTerm t n s * (gauss u : ℂ)‖ ≤
      ‖mainTerm t n s‖ * ((Real.exp (κ * u ^ 2 + A) - 1) * gauss u) := by
    intro u
    obtain ⟨δ, hδ, heq⟩ := exists_shifted_eq ht0 ht hn hs u
    have heq' : Fc (u + c) = mainTerm t n s * Complex.exp δ * (gauss u : ℂ) := by
      rw [hFc, hc, hαn]; exact heq
    rw [heq']
    have hg : 0 ≤ gauss u := by unfold gauss; positivity
    calc ‖mainTerm t n s * Complex.exp δ * (gauss u : ℂ) - mainTerm t n s * (gauss u : ℂ)‖
        = ‖mainTerm t n s‖ * (‖Complex.exp δ - 1‖ * gauss u) := by
          rw [show mainTerm t n s * Complex.exp δ * (gauss u : ℂ) - mainTerm t n s * (gauss u : ℂ)
              = mainTerm t n s * ((Complex.exp δ - 1) * (gauss u : ℂ)) by ring,
            norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
      _ ≤ ‖mainTerm t n s‖ * ((Real.exp (κ * u ^ 2 + A) - 1) * gauss u) := by
          gcongr
          refine (norm_exp_sub_one_le_exp_norm_sub_one δ).trans ?_
          gcongr
  -- integrability
  have hint1 : Integrable fun u : ℝ => Fc (u + c) := by
    obtain ⟨C, hC⟩ := exists_strip_bound ht hn hs hcim
    have hcont : Continuous fun u : ℝ => Fc (u + c.im * I) := by
      rw [hFc]
      refine Continuous.mul ?_ (by fun_prop)
      refine continuous_iff_continuousAt.2 fun u => ?_
      have him : (s + Real.sqrt t * ((u : ℂ) + c.im * I)).im ≠ 0 := by
        rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
        have : Real.sqrt t * |c.im| ≤ 1 := by
          calc Real.sqrt t * |c.im| ≤ 1 * 1 := by gcongr
            _ = 1 := one_mul 1
        have := neg_abs_le c.im
        nlinarith
      exact (differentiableAt_r₀ hn him).continuousAt.comp
        (f := fun u : ℝ => s + Real.sqrt t * ((u : ℂ) + c.im * I)) (by fun_prop)
    have hI : Integrable fun u : ℝ => Fc (u + c.im * I) := by
      refine Integrable.mono'
        ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul C)
        hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
      have := hC ((u : ℂ) + c.im * I) (by simp)
      simpa [hFc] using this
    have := hI.comp_add_right c.re
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only
    congr 1
    push_cast
    rw [add_assoc, Complex.re_add_im]
  have hint2 : Integrable fun u : ℝ => mainTerm t n s * (gauss u : ℂ) :=
    integrable_gauss.ofReal.const_mul _
  have hint3 : Integrable fun u : ℝ => Real.exp (κ * u ^ 2 + A) * gauss u :=
    integrable_exp_mul_gauss A hκ1
  have hint4 : Integrable gauss := integrable_gauss
  -- assemble
  have hmain : ∫ u : ℝ, mainTerm t n s * (gauss u : ℂ) = mainTerm t n s := by
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal, integral_gauss]
    simp
  rw [hr, ← hmain, ← MeasureTheory.integral_sub hint1 hint2]
  refine (MeasureTheory.norm_integral_le_of_norm_le
    ((hint3.sub hint4).const_mul ‖mainTerm t n s‖) (Eventually.of_forall fun u => ?_)).trans ?_
  · have := hpt u
    simpa [sub_mul] using this
  · have hsub : ((fun u : ℝ => Real.exp (κ * u ^ 2 + A) * gauss u) - gauss) =
        fun u => Real.exp (κ * u ^ 2 + A) * gauss u - gauss u := rfl
    rw [MeasureTheory.integral_const_mul, hsub, MeasureTheory.integral_sub hint3 hint4,
      integral_exp_mul_gauss hκ1, integral_gauss, hmain]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [epsR]
    have h1 : Real.exp A / Real.sqrt (1 - κ) ≤ Real.exp A * Real.exp (t / (4 * (s.im - 3.33))) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (inv_sqrt_le_exp ht0 ht hs) (Real.exp_pos _).le
    have h2 : Real.exp A * Real.exp (t / (4 * (s.im - 3.33))) =
        Real.exp ((t ^ 2 / 8 * ‖alpha s - Real.log n‖ ^ 2 + t / 4 + 1 / 6) / (s.im - 3.33)) := by
      rw [← Real.exp_add, hA, hαn]
      congr 1
      field_simp
      ring
    linarith

end DeBruijnNewman
