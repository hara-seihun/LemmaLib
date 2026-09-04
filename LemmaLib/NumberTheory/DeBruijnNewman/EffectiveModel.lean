/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The effective Riemann–Siegel model of `H t` for large `x`

This file defines the objects of Theorem 1.3 of Polymath, *Effective approximation of heat flow
evolution of the Riemann ξ function*, Res. Math. Sci. 6 (2019): the Stirling-type factor `M₀`, its
logarithmic derivative `alpha`, the deformed factor `M t`, the normalisation `B t`, the cutoff `N`,
the two Riemann–Siegel-type sums `f`, and the explicit error bounds `errAB` and `errC0`.

In the region `0 ≤ t ≤ 1/2`, `0 ≤ y ≤ 1`, `x ≥ 200` the theorem asserts

`H t (x + iy) = B t (x + iy) * (f t x y + O_≤ (errAB t x y + errC0 t x y))`.

The statement is recorded as the proposition `EffectiveApproximation`. It is derived in
`LemmaLib.NumberTheory.DeBruijnNewman.EffectiveApproximation` from the two Riemann–Siegel inputs
`RtnEstimate` and `TailEstimate` of `LemmaLib.NumberTheory.DeBruijnNewman.RiemannSiegel` (Polymath
Propositions 6.1 and 6.3). `RtnEstimate` is proved in
`LemmaLib.NumberTheory.DeBruijnNewman.RtnEstimate`; `TailEstimate`, whose proof goes through
Arias de Reyna's explicit remainder bounds for the Riemann–Siegel expansion, is not yet
formalised. Everything the consumer needs on top of it is proved here: `B t` never vanishes on the region, so the nonvanishing test
`errAB + errC0 < ‖f‖ → H t (x + iy) ≠ 0` follows, and the explicit bounds on `‖gamma‖`, `Re sStar`
and `‖kappa‖` hold unconditionally.
-/

public section

open Complex Real Finset

namespace DeBruijnNewman

/-- `α(s) = 1/(2s) + 1/(s-1) + ½ Log (s/(2π))`, the logarithmic derivative of `M₀`. -/
@[expose] noncomputable def alpha (s : ℂ) : ℂ :=
  1 / (2 * s) + 1 / (s - 1) + 1 / 2 * Complex.log (s / (2 * π))

/-- The derivative of `alpha`: `α'(s) = -1/(2s²) - 1/(s-1)² + 1/(2s)`. -/
@[expose] noncomputable def alpha' (s : ℂ) : ℂ :=
  -(1 / (2 * s ^ 2)) - 1 / (s - 1) ^ 2 + 1 / (2 * s)

/-- Stirling's approximation to `(1/8) (s(s-1)/2) π^{-s/2} Γ(s/2)`:
`M₀(s) = (s(s-1)/16) π^{-s/2} √(2π) exp ((s/2 - 1/2) Log (s/2) - s/2)`. -/
@[expose] noncomputable def M₀ (s : ℂ) : ℂ :=
  s * (s - 1) / 16 * (π : ℂ) ^ (-s / 2) * (Real.sqrt (2 * π) : ℂ) *
    Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2)

/-- The holomorphic branch of `log M₀` on `ℂ \ (-∞, 1]` used by Polymath (their (1.6)). -/
@[expose] noncomputable def logM₀ (s : ℂ) : ℂ :=
  Complex.log s + Complex.log (s - 1) - s / 2 * Real.log π + Real.log (Real.sqrt (2 * π) / 16) +
    (s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2

/-- The heat deformation `M_t(s) = exp (t α(s)² / 4) M₀(s)`. -/
@[expose] noncomputable def M (t : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (t / 4 * alpha s ^ 2) * M₀ s

/-- The normalising factor `B_t(x+iy) = M_t((1+y-ix)/2)`, written as `M_t((1 - iz)/2)`. -/
@[expose] noncomputable def B (t : ℝ) (z : ℂ) : ℂ :=
  M t ((1 - I * z) / 2)

/-- `s₊ = (1 + y - ix)/2`. -/
@[expose] noncomputable def sPlus (x y : ℝ) : ℂ := (1 + y - x * I) / 2

/-- `s₋ = (1 - y + ix)/2 = 1 - s₊`. -/
@[expose] noncomputable def sMinus (x y : ℝ) : ℂ := (1 - y + x * I) / 2

/-- The Riemann–Siegel cutoff `N = ⌊√(x/(4π) + t/16)⌋`. -/
@[expose] noncomputable def cutoff (t x : ℝ) : ℕ := ⌊Real.sqrt (x / (4 * π) + t / 16)⌋₊

/-- The heat-flow coefficients `b_n^t = exp (t log² n / 4)`. -/
@[expose] noncomputable def b (t : ℝ) (n : ℕ) : ℝ := Real.exp (t / 4 * Real.log n ^ 2)

/-- `s_* = s₊ + (t/2) α(s₊)`. -/
@[expose] noncomputable def sStar (t x y : ℝ) : ℂ := sPlus x y + t / 2 * alpha (sPlus x y)

/-- `κ = (t/2) (α((1-y+ix)/2) - α((1+y+ix)/2))`. -/
@[expose] noncomputable def kappa (t x y : ℝ) : ℂ :=
  t / 2 * (alpha ((1 - y + x * I) / 2) - alpha ((1 + y + x * I) / 2))

/-- `γ = M_t((1-y+ix)/2) / M_t((1+y-ix)/2)`. -/
@[expose] noncomputable def gamma (t x y : ℝ) : ℂ :=
  M t ((1 - y + x * I) / 2) / M t ((1 + y - x * I) / 2)

/-- The two Riemann–Siegel-type sums
`f_t(x+iy) = ∑_{n=1}^N b_n^t / n^{s_*} + γ ∑_{n=1}^N n^y b_n^t / n^{conj s_* + κ}`. -/
@[expose] noncomputable def f (t x y : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 (cutoff t x), (b t n : ℂ) / (n : ℂ) ^ sStar t x y +
    gamma t x y * ∑ n ∈ Icc 1 (cutoff t x),
      (n : ℂ) ^ (y : ℂ) * (b t n : ℂ) / (n : ℂ) ^ ((starRingEnd ℂ) (sStar t x y) + kappa t x y)

/-- The bound `e_A + e_B ≤ ∑_{n=1}^N (1 + |γ| N^{|κ|} n^y) b_n^t n^{-Re s_*}
(exp ((t²/16 log² (x/(4πn²)) + 0.626) / (x - 6.66)) - 1)` of Polymath (1.14). -/
@[expose] noncomputable def errAB (t x y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 (cutoff t x),
    (1 + ‖gamma t x y‖ * (cutoff t x : ℝ) ^ ‖kappa t x y‖ * (n : ℝ) ^ y) *
      b t n / (n : ℝ) ^ (sStar t x y).re *
      (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66)) - 1)

/-- The bound `e_{C,0} ≤ (x/4π)^{-(1+y)/4} exp (-(t/16) log² (x/4π) + 1.24 (3^y + 3^{-y}) / (N - 0.125)
+ (3 |log (x/4π) + iπ/2| + 10.44) / (x - 12))` of Polymath (1.15). -/
@[expose] noncomputable def errC0 (t x y : ℝ) : ℝ :=
  (x / (4 * π)) ^ (-(1 + y) / 4) *
    Real.exp (-(t / 16) * Real.log (x / (4 * π)) ^ 2 +
      1.24 * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) / ((cutoff t x : ℝ) - 0.125) +
      (3 * Real.sqrt (Real.log (x / (4 * π)) ^ 2 + (π / 2) ^ 2) + 10.44) / (x - 12))

theorem errC0_nonneg {t x y : ℝ} (hx : 0 ≤ x) : 0 ≤ errC0 t x y := by
  unfold errC0
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ x / (4 * π) by positivity) (-(1 + y) / 4)
  positivity

/-- The region of Polymath Theorem 1.3, with `t = 0` included (the theorem is stated there for
`t > 0`; the `t = 0` case follows by continuity in `t`, since `N` is right-continuous in `t`). -/
structure InRegion (t x y : ℝ) : Prop where
  t_nonneg : 0 ≤ t
  t_le : t ≤ 1 / 2
  y_nonneg : 0 ≤ y
  y_le : y ≤ 1
  x_ge : 200 ≤ x

/-- Polymath Theorem 1.3 in multiplicative form with the tail constant `K`: on the region,
`‖H_t(x+iy) - B_t(x+iy) f_t(x+iy)‖ ≤ ‖B_t(x+iy)‖ (e_A + e_B + K e_{C,0})`, with the error terms
replaced by the explicit upper bounds (1.14) and (1.15). -/
@[expose] def EffectiveApproximationWith (K : ℝ) : Prop :=
  ∀ t x y : ℝ, InRegion t x y →
    ‖H t (x + y * I) - B t (x + y * I) * f t x y‖ ≤
      ‖B t (x + y * I)‖ * (errAB t x y + K * errC0 t x y)

/-- Polymath Theorem 1.3 as stated, with the tail constant `1`. -/
@[expose] def EffectiveApproximation : Prop := EffectiveApproximationWith 1

theorem EffectiveApproximationWith.mono {K K' : ℝ} (hK : K ≤ K') (h : EffectiveApproximationWith K) :
    EffectiveApproximationWith K' := fun t x y hr =>
  (h t x y hr).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hK (errC0_nonneg (by linarith [hr.x_ge]))))
    (norm_nonneg _))

/-! ### `B t` never vanishes -/

theorem B_apply (t x y : ℝ) : B t (x + y * I) = M t (sPlus x y) := by
  unfold B sPlus
  congr 1
  apply Complex.ext <;> simp

theorem M₀_ne_zero {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : M₀ s ≠ 0 := by
  unfold M₀
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hsq : (Real.sqrt (2 * π) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by simp [h0, hs1])
    (fun h => hpi ((cpow_eq_zero_iff _ _).mp h).1)) hsq) (Complex.exp_ne_zero _)

theorem M_ne_zero (t : ℝ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : M t s ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (M₀_ne_zero h0 h1)

/-- `B_t(z) ≠ 0` whenever `Re z ≠ 0`; in particular on the whole region. -/
theorem B_ne_zero (t : ℝ) {z : ℂ} (hz : z.re ≠ 0) : B t z ≠ 0 := by
  refine M_ne_zero t ?_ ?_
  · intro h
    have := congrArg Complex.im h
    simp at this
    exact hz this
  · intro h
    have := congrArg Complex.im h
    simp at this
    exact hz this

/-! ### The nonvanishing test -/

/-- Polymath Corollary 1.4: if `|f_t(x+iy)| > e_A + e_B + K e_{C,0}` then `H_t(x+iy) ≠ 0`. This
is the only consequence of Theorem 1.3 the certificate uses. -/
theorem H_ne_zero_of_lt_norm_f {K : ℝ} (happrox : EffectiveApproximationWith K) {t x y : ℝ}
    (hr : InRegion t x y) (hf : errAB t x y + K * errC0 t x y < ‖f t x y‖) :
    H t (x + y * I) ≠ 0 := by
  intro hH
  have hB : B t (x + y * I) ≠ 0 := B_ne_zero t (by simp; linarith [hr.x_ge])
  have hBpos : 0 < ‖B t (x + y * I)‖ := norm_pos_iff.mpr hB
  have h := happrox t x y hr
  rw [hH, zero_sub, norm_neg, norm_mul] at h
  have := le_of_mul_le_mul_left h hBpos
  linarith

/-! ### Derivatives of `alpha` and of the logarithm of `M` -/

theorem mem_slitPlane_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : s ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr h)

theorem div_two_pi_im (s : ℂ) : (s / (2 * π)).im = s.im / (2 * π) := by
  rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_im]

theorem hasDerivAt_alpha {s : ℂ} (hs : s.im ≠ 0) : HasDerivAt alpha (alpha' s) s := by
  have h0 : s ≠ 0 := fun h => hs (by simp [h])
  have h1 : s - 1 ≠ 0 := fun h => hs (by simpa using congrArg Complex.im h)
  have hslit : s / (2 * π) ∈ slitPlane := by
    apply mem_slitPlane_of_im_ne_zero
    rw [div_two_pi_im]
    exact div_ne_zero hs (by positivity)
  have hA : HasDerivAt (fun s : ℂ => 1 / (2 * s)) (-(1 / (2 * s ^ 2))) s := by
    have h := ((hasDerivAt_id s).const_mul (2 : ℂ)).inv (by simpa using h0)
    have e : (fun s : ℂ => 1 / (2 * s)) = (fun y => 2 * id y)⁻¹ := by funext w; simp [one_div]
    rw [e]
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hB : HasDerivAt (fun s : ℂ => 1 / (s - 1)) (-(1 / (s - 1) ^ 2)) s := by
    have h := ((hasDerivAt_id s).sub_const (1 : ℂ)).inv h1
    have e : (fun s : ℂ => 1 / (s - 1)) = (fun y => id y - 1)⁻¹ := by funext w; simp [one_div]
    rw [e]
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hC : HasDerivAt (fun s : ℂ => 1 / 2 * Complex.log (s / (2 * π))) (1 / (2 * s)) s := by
    have h := (((hasDerivAt_id s).div_const (2 * (π : ℂ))).clog hslit).const_mul (1 / 2 : ℂ)
    simp only [id] at h
    refine h.congr_deriv ?_
    field_simp
  exact (hA.add hB).add hC

/-- Polymath (6.2): `|α'(s)| ≤ 1 / (2 Im s - 6)` when `Im s > 3`. -/
theorem norm_alpha'_le {s : ℂ} (hs : 3 < s.im) : ‖alpha' s‖ ≤ 1 / (2 * s.im - 6) := by
  have hT : 0 < s.im := by linarith
  have hsn : s.im ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    rw [abs_of_pos hT] at this
    exact this
  have hs1 : s.im ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero, abs_of_pos hT] at this
    exact this
  have e1 : ‖-(1 / (2 * s ^ 2))‖ ≤ 1 / (2 * s.im ^ 2) := by
    rw [norm_neg, norm_div, norm_one, norm_mul, norm_pow]
    simp only [Complex.norm_ofNat]
    gcongr
  have e2 : ‖1 / (s - 1) ^ 2‖ ≤ 1 / s.im ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    gcongr
  have e3 : ‖1 / (2 * s)‖ ≤ 1 / (2 * s.im) := by
    rw [norm_div, norm_one, norm_mul]
    simp only [Complex.norm_ofNat]
    gcongr
  calc ‖alpha' s‖ ≤ ‖-(1 / (2 * s ^ 2))‖ + ‖1 / (s - 1) ^ 2‖ + ‖1 / (2 * s)‖ := by
        unfold alpha'
        exact (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ 1 / (2 * s.im ^ 2) + 1 / s.im ^ 2 + 1 / (2 * s.im) := by gcongr
    _ ≤ 1 / (2 * s.im - 6) := by
        rw [div_add_div _ _ (by positivity) (by positivity),
          div_add_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by linarith)]
        nlinarith [hT]

theorem log_div_two_pi {s : ℂ} (hs : s ≠ 0) :
    Complex.log (s / (2 * π)) = Complex.log (s / 2) - Real.log π := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have e : s / (2 * π) = ((π⁻¹ : ℝ) : ℂ) * (s / 2) := by
    push_cast; field_simp
  apply Complex.ext
  · rw [Complex.sub_re, Complex.log_re, Complex.log_re, e, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpi), Complex.ofReal_re,
      Real.log_mul (inv_pos.mpr hpi).ne' (by simp [hs]), Real.log_inv]
    ring
  · rw [Complex.sub_im, Complex.log_im, Complex.log_im, e, Complex.arg_real_mul _ (inv_pos.mpr hpi),
      Complex.ofReal_im, sub_zero]

theorem hasDerivAt_logM₀ {s : ℂ} (hs : s.im ≠ 0) : HasDerivAt logM₀ (alpha s) s := by
  have h0 : s ≠ 0 := fun h => hs (by simp [h])
  have hslit : s ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr hs)
  have hslit1 : s - 1 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by simpa using hs))
  have hslit2 : s / 2 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by simpa using hs))
  have hA : HasDerivAt (fun s : ℂ => Complex.log s) s⁻¹ s := Complex.hasDerivAt_log hslit
  have hB : HasDerivAt (fun s : ℂ => Complex.log (s - 1)) ((s - 1)⁻¹) s := by
    have := ((hasDerivAt_id s).sub_const (1 : ℂ)).clog hslit1
    simpa using this
  have hC : HasDerivAt (fun s : ℂ => s / 2 * (Real.log π : ℂ)) ((Real.log π : ℂ) / 2) s := by
    have := ((hasDerivAt_id s).div_const (2 : ℂ)).mul_const (Real.log π : ℂ)
    simpa [div_eq_mul_inv, mul_comm] using this
  have hD : HasDerivAt (fun s : ℂ => (s / 2 - 1 / 2) * Complex.log (s / 2))
      (1 / 2 * Complex.log (s / 2) + (s / 2 - 1 / 2) * ((1 / 2) / (s / 2))) s := by
    have h1' : HasDerivAt (fun s : ℂ => s / 2 - 1 / 2) (1 / 2) s := by
      have := ((hasDerivAt_id s).div_const (2 : ℂ)).sub_const (1 / 2 : ℂ)
      simpa using this
    have h2' : HasDerivAt (fun s : ℂ => Complex.log (s / 2)) ((1 / 2) / (s / 2)) s := by
      have := ((hasDerivAt_id s).div_const (2 : ℂ)).clog hslit2
      simpa using this
    exact h1'.mul h2'
  have hE : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const (2 : ℂ)
  have := ((((hA.add hB).sub hC).add_const (Real.log (Real.sqrt (2 * π) / 16) : ℂ)).add hD).sub hE
  unfold logM₀
  refine this.congr_deriv ?_
  unfold alpha
  rw [log_div_two_pi h0]
  field_simp
  ring

theorem M₀_eq_exp_logM₀ {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : M₀ s = Complex.exp (logM₀ s) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsq : 0 < Real.sqrt (2 * π) / 16 := by positivity
  unfold M₀ logM₀
  simp only [Complex.exp_add, Complex.exp_sub]
  rw [Complex.exp_log h0, Complex.exp_log hs1, Complex.cpow_def_of_ne_zero hpi,
    ← Complex.ofReal_log Real.pi_pos.le, ← Complex.ofReal_exp, Real.exp_log hsq]
  push_cast
  field_simp
  rw [Complex.exp_neg]
  ring_nf
  exact mul_inv_cancel₀ (Complex.exp_ne_zero _)

theorem norm_M₀ {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : ‖M₀ s‖ = Real.exp (logM₀ s).re := by
  rw [M₀_eq_exp_logM₀ h0 h1, Complex.norm_exp]

/-- The holomorphic logarithm of `M t`: `log M_t(s) = (t/4) α(s)² + log M₀(s)`. -/
@[expose] noncomputable def logM (t : ℝ) (s : ℂ) : ℂ := t / 4 * alpha s ^ 2 + logM₀ s

theorem norm_M {t : ℝ} {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : ‖M t s‖ = Real.exp (logM t s).re := by
  unfold M logM
  rw [norm_mul, Complex.norm_exp, norm_M₀ h0 h1, ← Real.exp_add, Complex.add_re]

theorem hasDerivAt_logM {t : ℝ} {s : ℂ} (hs : s.im ≠ 0) :
    HasDerivAt (logM t) (t / 2 * alpha s * alpha' s + alpha s) s := by
  have h1 := ((hasDerivAt_alpha hs).pow 2).const_mul (t / 4 : ℂ)
  have := h1.add (hasDerivAt_logM₀ hs)
  unfold logM
  refine this.congr_deriv ?_
  push_cast; ring

theorem arg_ne_pi_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s.arg ≠ π := fun h =>
  hs (Complex.arg_eq_pi_iff.mp h).2

theorem alpha_conj {s : ℂ} (hs : s.im ≠ 0) :
    alpha ((starRingEnd ℂ) s) = (starRingEnd ℂ) (alpha s) := by
  have h : (s / (2 * π)).im ≠ 0 := by
    rw [div_two_pi_im]
    exact div_ne_zero hs (by positivity)
  unfold alpha
  simp only [map_add, map_mul, map_div₀, map_one, map_sub, map_ofNat]
  rw [← Complex.log_conj _ (arg_ne_pi_of_im_ne_zero h)]
  simp only [map_div₀, Complex.conj_ofReal, map_mul, map_ofNat]

theorem logM₀_conj {s : ℂ} (hs : s.im ≠ 0) :
    logM₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logM₀ s) := by
  have h1 : (s - 1).im ≠ 0 := by simpa using hs
  have h2 : (s / 2).im ≠ 0 := by simpa using hs
  unfold logM₀
  simp only [map_add, map_mul, map_div₀, map_one, map_sub, Complex.conj_ofReal, map_ofNat]
  rw [← Complex.log_conj _ (arg_ne_pi_of_im_ne_zero hs),
    ← Complex.log_conj _ (arg_ne_pi_of_im_ne_zero h1), ← Complex.log_conj _ (arg_ne_pi_of_im_ne_zero h2)]
  simp only [map_div₀, map_sub, map_one, map_ofNat]

/-- `|M_t(conj s)| = |M_t(s)|`, in logarithmic form. -/
theorem logM_conj_re {t : ℝ} {s : ℂ} (hs : s.im ≠ 0) :
    (logM t ((starRingEnd ℂ) s)).re = (logM t s).re := by
  unfold logM
  rw [alpha_conj hs, logM₀_conj hs, ← map_pow]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp

/-! ### Points on a horizontal line -/

theorem norm_horizontal (σ c : ℝ) : ‖(σ : ℂ) + c * I‖ = Real.sqrt (σ ^ 2 + c ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]; simp; ring_nf

theorem conj_horizontal (a c : ℝ) :
    (starRingEnd ℂ) ((a : ℂ) + (c : ℂ) * I) = (a : ℂ) - (c : ℂ) * I := by
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring

theorem sMinus_eq (x y : ℝ) :
    ((1 - y + x * I) / 2 : ℂ) = (((1 - y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

theorem sPlus_eq_conj (x y : ℝ) :
    ((1 + y - x * I) / 2 : ℂ) = (starRingEnd ℂ) ((((1 + y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I) := by
  rw [conj_horizontal]
  apply Complex.ext <;> simp; ring

/-- `Re α(σ + ic)` in real terms. -/
theorem re_alpha (σ c : ℝ) (hc : c ≠ 0) :
    (alpha (σ + c * I)).re = σ / (2 * (σ ^ 2 + c ^ 2)) + (σ - 1) / ((σ - 1) ^ 2 + c ^ 2)
      + 1 / 4 * Real.log (σ ^ 2 + c ^ 2) - 1 / 2 * Real.log (2 * π) := by
  have hA : 0 < σ ^ 2 + c ^ 2 := by positivity
  have hpi : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  have h1 : (1 / (2 * ((σ : ℂ) + c * I))).re = σ / (2 * (σ ^ 2 + c ^ 2)) := by
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp
  have h2 : (1 / ((σ : ℂ) + c * I - 1)).re = (σ - 1) / ((σ - 1) ^ 2 + c ^ 2) := by
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    ring
  have h3 : (1 / 2 * Complex.log (((σ : ℂ) + c * I) / (2 * π))).re
      = 1 / 4 * Real.log (σ ^ 2 + c ^ 2) - 1 / 2 * Real.log (2 * π) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, Complex.log_re,
      hpi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_horizontal,
      Real.log_div (by positivity) (by positivity), Real.log_sqrt hA.le]
    ring
  unfold alpha
  rw [Complex.add_re, Complex.add_re, h1, h2, h3]
  ring

theorem hasDerivAt_alpha_horizontal {c : ℝ} (hc : c ≠ 0) (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => alpha (σ + c * I)) (alpha' (σ + c * I)) σ := by
  have h : HasDerivAt (fun z : ℂ => alpha (z + c * I)) (alpha' (σ + c * I)) σ := by
    have h1 : HasDerivAt (fun z : ℂ => z + c * I) 1 (σ : ℂ) := (hasDerivAt_id _).add_const _
    have h2 := hasDerivAt_alpha (s := (σ : ℂ) + c * I) (by simp [hc])
    have h3 := h2.comp (σ : ℂ) h1
    rw [mul_one] at h3
    exact h3
  exact h.comp_ofReal

theorem hasDerivAt_logM_re_horizontal {t c : ℝ} (hc : c ≠ 0) (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => (logM t (σ + c * I)).re)
      (t / 2 * alpha (σ + c * I) * alpha' (σ + c * I) + alpha (σ + c * I)).re σ := by
  have h : HasDerivAt (fun z : ℂ => logM t (z + c * I))
      (t / 2 * alpha (σ + c * I) * alpha' (σ + c * I) + alpha (σ + c * I)) σ := by
    have h1 : HasDerivAt (fun z : ℂ => z + c * I) 1 (σ : ℂ) := (hasDerivAt_id _).add_const _
    have h2 := hasDerivAt_logM (t := t) (s := (σ : ℂ) + c * I) (by simp [hc])
    have h3 := h2.comp (σ : ℂ) h1
    rw [mul_one] at h3
    exact h3
  exact h.real_of_complex

/-! ### The bound on `κ` -/

theorem norm_alpha_sub_alpha_le {c a b : ℝ} (hc : 3 < c) (hab : a ≤ b) :
    ‖alpha (b + c * I) - alpha (a + c * I)‖ ≤ 1 / (2 * c - 6) * (b - a) := by
  have hc0 : c ≠ 0 := by linarith
  refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun σ : ℝ => alpha (σ + c * I))
    (f' := fun σ : ℝ => alpha' (σ + c * I))
    (fun σ _ => (hasDerivAt_alpha_horizontal hc0 σ).hasDerivWithinAt) (fun σ _ => ?_) b ⟨hab, le_rfl⟩
  have := norm_alpha'_le (s := (σ : ℂ) + c * I) (by simpa using hc)
  simpa using this

/-- Polymath (1.13): `|κ| ≤ t y / (2 (x - 6))`. -/
theorem norm_kappa_le {t x y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) (hx : 6 < x) :
    ‖kappa t x y‖ ≤ t * y / (2 * (x - 6)) := by
  have hc : 3 < x / 2 := by linarith
  have e1 : ((1 - y + x * I) / 2 : ℂ) = (((1 - y) / 2 : ℝ) : ℂ) + (x / 2 : ℝ) * I := by
    apply Complex.ext <;> simp
  have e2 : ((1 + y + x * I) / 2 : ℂ) = (((1 + y) / 2 : ℝ) : ℂ) + (x / 2 : ℝ) * I := by
    apply Complex.ext <;> simp
  have h := norm_alpha_sub_alpha_le (c := x / 2) (a := (1 - y) / 2) (b := (1 + y) / 2) hc (by linarith)
  unfold kappa
  rw [e1, e2, norm_mul, ← norm_neg (alpha _ - alpha _), neg_sub]
  have hn : ‖(t / 2 : ℂ)‖ = t / 2 := by
    rw [show (t / 2 : ℂ) = ((t / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  rw [hn]
  calc t / 2 * ‖alpha (↑((1 + y) / 2) + ↑(x / 2) * I) - alpha (↑((1 - y) / 2) + ↑(x / 2) * I)‖
      ≤ t / 2 * (1 / (2 * (x / 2) - 6) * ((1 + y) / 2 - (1 - y) / 2)) := by gcongr
    _ = t * y / (2 * (x - 6)) := by field_simp; ring

/-! ### The bound on `Re s_*` -/

theorem normSq_sPlus (x y : ℝ) : Complex.normSq (sPlus x y) = ((1 + y) ^ 2 + x ^ 2) / 4 := by
  unfold sPlus
  rw [Complex.normSq_apply]
  simp
  ring

theorem norm_sPlus (x y : ℝ) : ‖sPlus x y‖ = Real.sqrt ((1 + y) ^ 2 + x ^ 2) / 2 := by
  rw [Complex.norm_def, normSq_sPlus, Real.sqrt_div (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem re_alpha_sPlus (x y : ℝ) (hx : 0 < x) :
    (alpha (sPlus x y)).re = (1 + y) / ((1 + y) ^ 2 + x ^ 2) - 2 * (1 - y) / ((1 - y) ^ 2 + x ^ 2)
      + 1 / 4 * Real.log (((1 + y) ^ 2 + x ^ 2) / 4) - 1 / 2 * Real.log (2 * π) := by
  have hA : 0 < (1 + y) ^ 2 + x ^ 2 := by positivity
  have hpi : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  have h1 : (1 / (2 * sPlus x y)).re = (1 + y) / ((1 + y) ^ 2 + x ^ 2) := by
    unfold sPlus
    rw [show (2 : ℂ) * ((1 + y - x * I) / 2) = 1 + y - x * I by ring, Complex.div_re]
    simp [Complex.normSq_apply]
    ring
  have h2 : (1 / (sPlus x y - 1)).re = -(2 * (1 - y) / ((1 - y) ^ 2 + x ^ 2)) := by
    unfold sPlus
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp
    ring
  have h3 : (1 / 2 * Complex.log (sPlus x y / (2 * π))).re
      = 1 / 4 * Real.log (((1 + y) ^ 2 + x ^ 2) / 4) - 1 / 2 * Real.log (2 * π) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, Complex.log_re,
      hpi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_sPlus,
      Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by norm_num),
      Real.log_sqrt hA.le, Real.log_div hA.ne' (by norm_num)]
    have : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]
    ring
  unfold alpha
  rw [Complex.add_re, Complex.add_re, h1, h2, h3]
  ring

/-- The rational part of `Re α(s₊)` together with a quarter of `log (|2s₊|²/x²)` is at least
`-(1-3y)₊/x²`; this absorbs the `8y(1-y)/x²` correction of Polymath Proposition 6.6(ii). -/
theorem re_alpha_sPlus_rational_ge {x y : ℝ} (hx : 3 ≤ x) (hy0 : 0 ≤ y) :
    -(max (1 - 3 * y) 0 / x ^ 2) ≤ (1 + y) / ((1 + y) ^ 2 + x ^ 2) - 2 * (1 - y) / ((1 - y) ^ 2 + x ^ 2)
      + 1 / (4 * ((1 + y) ^ 2 + x ^ 2)) := by
  set A := (1 + y) ^ 2 + x ^ 2 with hA
  set B := (1 - y) ^ 2 + x ^ 2 with hB
  set m := max (1 - 3 * y) 0 with hm
  have hx0 : 0 < x := by linarith
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hAx : x ^ 2 ≤ A := by rw [hA]; nlinarith
  have hBx : x ^ 2 ≤ B := by rw [hB]; nlinarith
  have hx9 : 9 ≤ x ^ 2 := by nlinarith
  have hpoly : (1 - y ^ 2) * (1 + 3 * y) ≤ 9 / 4 := by
    nlinarith [sq_nonneg (y - 1 / 2), mul_nonneg hy0 (sq_nonneg (y - 1 / 2))]
  have hB4 : 0 ≤ B / 4 - (1 - y ^ 2) * (1 + 3 * y) := by linarith
  rw [neg_le_iff_add_nonneg', add_comm]
  have key : (1 + y) / A - 2 * (1 - y) / B + 1 / (4 * A) + m / x ^ 2
      = ((1 + y) * B * x ^ 2 - 2 * (1 - y) * A * x ^ 2 + B * x ^ 2 / 4 + m * A * B) / (A * B * x ^ 2) := by
    field_simp
  rw [key]
  apply div_nonneg _ (by positivity)
  rcases le_or_gt (1 - 3 * y) 0 with h | h
  · have hm0 : m = 0 := by rw [hm]; exact max_eq_right h
    have e : (1 + y) * B * x ^ 2 - 2 * (1 - y) * A * x ^ 2 + B * x ^ 2 / 4 + m * A * B
        = x ^ 4 * (3 * y - 1) + x ^ 2 * (B / 4 - (1 - y ^ 2) * (1 + 3 * y)) := by
      rw [hm0, hA, hB]; ring
    rw [e]
    have : 0 ≤ 3 * y - 1 := by linarith
    positivity
  · have hm0 : m = 1 - 3 * y := by rw [hm]; exact max_eq_left h.le
    have e : (1 + y) * B * x ^ 2 - 2 * (1 - y) * A * x ^ 2 + B * x ^ 2 / 4 + m * A * B
        = (1 - 3 * y) * (A * B - x ^ 4) + x ^ 2 * (B / 4 - (1 - y ^ 2) * (1 + 3 * y)) := by
      rw [hm0, hA, hB]; ring
    rw [e]
    have h1 : 0 ≤ A * B - x ^ 4 := by
      have : x ^ 2 * x ^ 2 ≤ A * B := mul_le_mul hAx hBx (by positivity) hApos.le
      nlinarith
    have h2 : 0 ≤ 1 - 3 * y := h.le
    positivity

theorem re_alpha_sPlus_ge {x y : ℝ} (hx : 3 ≤ x) (hy0 : 0 ≤ y) :
    1 / 2 * Real.log (x / (4 * π)) - max (1 - 3 * y) 0 / x ^ 2 ≤ (alpha (sPlus x y)).re := by
  have hx0 : 0 < x := by linarith
  rw [re_alpha_sPlus x y hx0]
  have hA : 0 < (1 + y) ^ 2 + x ^ 2 := by positivity
  have hlog : 1 / 4 * Real.log (((1 + y) ^ 2 + x ^ 2) / 4) - 1 / 2 * Real.log (2 * π)
      - 1 / 2 * Real.log (x / (4 * π)) = 1 / 4 * Real.log (((1 + y) ^ 2 + x ^ 2) / x ^ 2) := by
    rw [Real.log_div hA.ne' (by norm_num), Real.log_div hx0.ne' (by positivity),
      Real.log_div hA.ne' (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne',
      Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have hlog2 : 1 - x ^ 2 / ((1 + y) ^ 2 + x ^ 2) ≤ Real.log (((1 + y) ^ 2 + x ^ 2) / x ^ 2) := by
    have := Real.one_sub_inv_le_log_of_pos (x := ((1 + y) ^ 2 + x ^ 2) / x ^ 2) (by positivity)
    rwa [inv_div] at this
  have hlog3 : 1 / (4 * ((1 + y) ^ 2 + x ^ 2)) ≤ 1 / 4 * Real.log (((1 + y) ^ 2 + x ^ 2) / x ^ 2) := by
    have : 1 - x ^ 2 / ((1 + y) ^ 2 + x ^ 2) = (1 + y) ^ 2 / ((1 + y) ^ 2 + x ^ 2) := by
      field_simp
      ring
    have h1 : 1 / ((1 + y) ^ 2 + x ^ 2) ≤ (1 + y) ^ 2 / ((1 + y) ^ 2 + x ^ 2) := by
      gcongr
      nlinarith
    calc 1 / (4 * ((1 + y) ^ 2 + x ^ 2)) = 1 / 4 * (1 / ((1 + y) ^ 2 + x ^ 2)) := by
          rw [one_div_mul_one_div]
      _ ≤ 1 / 4 * ((1 + y) ^ 2 / ((1 + y) ^ 2 + x ^ 2)) := by gcongr
      _ ≤ _ := by rw [← this]; gcongr
  have := re_alpha_sPlus_rational_ge hx hy0
  linarith

theorem re_sStar (t x y : ℝ) : (sStar t x y).re = (1 + y) / 2 + t / 2 * (alpha (sPlus x y)).re := by
  unfold sStar sPlus
  simp [Complex.add_re, Complex.mul_re]

/-- The lower bound on `Re s_*`. This is sharper than Polymath (1.12): the correction inside the
positive part is `1 - 3y` alone. -/
theorem re_sStar_ge {t x y : ℝ} (ht : 0 ≤ t) (hx : 3 ≤ x) (hy0 : 0 ≤ y) :
    (1 + y) / 2 + t / 4 * Real.log (x / (4 * π)) - t / 2 * (max (1 - 3 * y) 0 / x ^ 2)
      ≤ (sStar t x y).re := by
  have h := re_alpha_sPlus_ge hx hy0
  rw [re_sStar]
  have := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ t / 2)
  linarith

/-- Polymath (1.12) as printed: `Re s_* ≥ (1+y)/2 + (t/4) log (x/4π) - (t/(2x²)) (1 - 3y + 4y(1+y)/x²)₊`. -/
theorem re_sStar_ge' {t x y : ℝ} (ht : 0 ≤ t) (hx : 3 ≤ x) (hy0 : 0 ≤ y) :
    (1 + y) / 2 + t / 4 * Real.log (x / (4 * π))
      - t / (2 * x ^ 2) * max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0 ≤ (sStar t x y).re := by
  have h := re_sStar_ge ht hx hy0
  have hx0 : 0 < x := by linarith
  have hmax : max (1 - 3 * y) 0 ≤ max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0 :=
    max_le_max (by have : 0 ≤ 4 * y * (1 + y) / x ^ 2 := by positivity
                   linarith) le_rfl
  have : t / 2 * (max (1 - 3 * y) 0 / x ^ 2) ≤ t / (2 * x ^ 2) * max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0 := by
    rw [show t / 2 * (max (1 - 3 * y) 0 / x ^ 2) = t / (2 * x ^ 2) * max (1 - 3 * y) 0 by
      field_simp]
    gcongr
  linarith

/-! ### The bound on `γ` -/

theorem re_alpha_horizontal_ge {σ x : ℝ} (hσ0 : 0 ≤ σ) (hx : 0 < x) :
    1 / 2 * Real.log (x / (4 * π)) - 4 / x ^ 2 ≤ (alpha (σ + (x / 2 : ℝ) * I)).re := by
  have hc : (x / 2) ≠ 0 := by positivity
  rw [re_alpha σ (x / 2) hc]
  have h1 : 0 ≤ σ / (2 * (σ ^ 2 + (x / 2) ^ 2)) := by positivity
  have h2 : -(4 / x ^ 2) ≤ (σ - 1) / ((σ - 1) ^ 2 + (x / 2) ^ 2) := by
    have hD : 0 < (σ - 1) ^ 2 + (x / 2) ^ 2 := by positivity
    rw [neg_le_iff_add_nonneg', div_add_div _ _ (by positivity) hD.ne']
    apply div_nonneg _ (by positivity)
    nlinarith [sq_nonneg (σ - 1), sq_nonneg x]
  have h3 : 1 / 2 * Real.log (x / 2) ≤ 1 / 4 * Real.log (σ ^ 2 + (x / 2) ^ 2) := by
    have : Real.log (x / 2) = 1 / 2 * Real.log ((x / 2) ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    rw [this]
    have := Real.log_le_log (by positivity : 0 < (x / 2) ^ 2)
      (by nlinarith : (x / 2) ^ 2 ≤ σ ^ 2 + (x / 2) ^ 2)
    linarith
  have h4 : Real.log (x / (4 * π)) = Real.log (x / 2) - Real.log (2 * π) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  rw [h4]
  linarith

theorem norm_alpha_horizontal_le {σ x : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hx : 200 ≤ x) :
    ‖alpha (σ + (x / 2 : ℝ) * I)‖ ≤ 3 / x + 1 / 2 * Real.log (x / (4 * π)) + 1 / x ^ 2 + π / 4 := by
  set w : ℂ := σ + (x / 2 : ℝ) * I with hw
  have hx0 : 0 < x := by linarith
  have hc : 0 < x / 2 := by positivity
  have hwn : x / 2 ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w
    rw [hw] at this ⊢
    simpa [abs_of_pos hc] using this
  have hw1 : x / 2 ≤ ‖w - 1‖ := by
    have := Complex.abs_im_le_norm (w - 1)
    rw [hw] at this ⊢
    simpa [abs_of_pos hc] using this
  have e1 : ‖1 / (2 * w)‖ ≤ 1 / x := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
    calc 1 / (2 * ‖w‖) ≤ 1 / (2 * (x / 2)) := by gcongr
      _ = 1 / x := by ring
  have e2 : ‖1 / (w - 1)‖ ≤ 2 / x := by
    rw [norm_div, norm_one]
    calc 1 / ‖w - 1‖ ≤ 1 / (x / 2) := by gcongr
      _ = 2 / x := by ring
  have hpi : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  have hnorm_w : ‖w‖ ≤ x / 2 + 1 / x := by
    rw [hw, norm_horizontal, Real.sqrt_le_left (by positivity)]
    have e : (x / 2 + 1 / x) ^ 2 = x ^ 2 / 4 + 1 + 1 / x ^ 2 := by field_simp; ring
    have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ 1 / x ^ 2 := by positivity
    rw [e]
    nlinarith
  have hre_nonneg : 0 ≤ Real.log (‖w‖ / (2 * π)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have := Real.pi_lt_d2
    linarith
  have hre_le : Real.log (‖w‖ / (2 * π)) ≤ Real.log (x / (4 * π)) + 2 / x ^ 2 := by
    have h1 : ‖w‖ / (2 * π) ≤ x / (4 * π) * (1 + 2 / x ^ 2) := by
      calc ‖w‖ / (2 * π) ≤ (x / 2 + 1 / x) / (2 * π) := by gcongr
        _ = x / (4 * π) * (1 + 2 / x ^ 2) := by field_simp; ring
    have h2 : Real.log (x / (4 * π) * (1 + 2 / x ^ 2))
        = Real.log (x / (4 * π)) + Real.log (1 + 2 / x ^ 2) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have h3 : Real.log (1 + 2 / x ^ 2) ≤ 2 / x ^ 2 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 2 / x ^ 2)
      linarith
    have hpos : 0 < ‖w‖ / (2 * π) := by
      apply div_pos _ (by positivity)
      exact lt_of_lt_of_le hc hwn
    calc Real.log (‖w‖ / (2 * π)) ≤ Real.log (x / (4 * π) * (1 + 2 / x ^ 2)) := Real.log_le_log hpos h1
      _ ≤ _ := by rw [h2]; linarith
  have harg : |(w / (2 * π)).arg| ≤ π / 2 := by
    rw [Complex.abs_arg_le_pi_div_two_iff, hpi, Complex.div_ofReal_re, hw]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    positivity
  have e3 : ‖1 / 2 * Complex.log (w / (2 * π))‖
      ≤ 1 / 2 * Real.log (x / (4 * π)) + 1 / x ^ 2 + π / 4 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
    have := Complex.norm_le_abs_re_add_abs_im (Complex.log (w / (2 * π)))
    rw [Complex.log_re, Complex.log_im, hpi, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_of_nonneg hre_nonneg] at this
    rw [← hpi] at this
    calc 1 / 2 * ‖Complex.log (w / (2 * π))‖
        ≤ 1 / 2 * (Real.log (‖w‖ / (2 * π)) + |(w / (2 * π)).arg|) := by gcongr
      _ ≤ 1 / 2 * ((Real.log (x / (4 * π)) + 2 / x ^ 2) + π / 2) := by gcongr
      _ = _ := by ring
  calc ‖alpha w‖ ≤ ‖1 / (2 * w)‖ + ‖1 / (w - 1)‖ + ‖1 / 2 * Complex.log (w / (2 * π))‖ := by
        unfold alpha
        exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ 1 / x + 2 / x + (1 / 2 * Real.log (x / (4 * π)) + 1 / x ^ 2 + π / 4) := by gcongr
    _ = _ := by ring

theorem log_div_four_pi_le {x : ℝ} (hx : 200 ≤ x) : Real.log (x / (4 * π)) ≤ x / 34 := by
  have hu : 0 < x / (4 * π) := by positivity
  have h1 : Real.log (x / (4 * π)) ≤ x / (4 * π) / Real.exp 1 := by
    have := Real.add_one_le_exp (x / (4 * π) / Real.exp 1 - 1)
    have h2 : x / (4 * π) ≤ Real.exp (x / (4 * π) / Real.exp 1) := by
      have e : Real.exp (x / (4 * π) / Real.exp 1 - 1)
          = Real.exp (x / (4 * π) / Real.exp 1) / Real.exp 1 := by
        rw [Real.exp_sub]
      rw [e] at this
      have hpos := Real.exp_pos 1
      rw [le_div_iff₀ hpos] at this
      calc x / (4 * π) = (x / (4 * π) / Real.exp 1 - 1 + 1) * Real.exp 1 := by field_simp; ring
        _ ≤ _ := this
    calc Real.log (x / (4 * π)) ≤ Real.log (Real.exp (x / (4 * π) / Real.exp 1)) :=
          Real.log_le_log hu h2
      _ = _ := Real.log_exp _
  have h3 : (34 : ℝ) ≤ 4 * π * Real.exp 1 := by
    have := Real.pi_gt_d2
    have := Real.exp_one_gt_d9
    nlinarith
  calc Real.log (x / (4 * π)) ≤ x / (4 * π) / Real.exp 1 := h1
    _ = x / (4 * π * Real.exp 1) := by rw [div_div]
    _ ≤ x / 34 := by gcongr

theorem gamma_numeric_bound {x : ℝ} (hx : 200 ≤ x) :
    4 / x ^ 2 + 1 / 4 * ((3 / x + 1 / 2 * (x / 34) + 1 / x ^ 2 + π / 4) / (x - 6)) ≤ 0.02 := by
  have hx0 : 0 < x := by linarith
  have hx6 : 0 < x - 6 := by linarith
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  rw [show 1 / 4 * ((3 / x + 1 / 2 * (x / 34) + 1 / x ^ 2 + π / 4) / (x - 6))
      = (3 * x + x ^ 3 / 68 + 1 + π * x ^ 2 / 4) / (4 * x ^ 2 * (x - 6)) by field_simp; ring]
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
  have h1 : 0 ≤ x ^ 2 * (x - 200) := by positivity
  have h2 : 0 ≤ x * (x - 200) := by positivity
  have h3 : 0 ≤ (3.15 - π) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  have key : 16 * (x - 6) + 3 * x + x ^ 3 / 68 + 1 + π * x ^ 2 / 4 ≤ 0.08 * x ^ 2 * (x - 6) := by
    nlinarith
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  nlinarith [mul_le_mul_of_nonneg_left key hx2]

/-- The derivative of `σ ↦ log |M_t(σ + ix/2)|` is at least `½ log (x/4π) - 0.02` on `0 ≤ σ ≤ 1`. -/
theorem re_deriv_logM_ge {t x σ : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hx : 200 ≤ x) :
    1 / 2 * Real.log (x / (4 * π)) - 0.02 ≤
      (t / 2 * alpha (σ + (x / 2 : ℝ) * I) * alpha' (σ + (x / 2 : ℝ) * I)
        + alpha (σ + (x / 2 : ℝ) * I)).re := by
  set w : ℂ := σ + (x / 2 : ℝ) * I with hw
  have hx0 : 0 < x := by linarith
  have hx6 : 0 < x - 6 := by linarith
  have hd : ‖alpha' w‖ ≤ 1 / (x - 6) := by
    calc ‖alpha' w‖ ≤ 1 / (2 * w.im - 6) := norm_alpha'_le (by rw [hw]; simp; linarith)
      _ = 1 / (x - 6) := by rw [hw]; simp; ring_nf
  have hα := norm_alpha_horizontal_le hσ0 hσ1 hx
  have hre := re_alpha_horizontal_ge hσ0 hx0
  have hL := log_div_four_pi_le hx
  have hnum := gamma_numeric_bound hx
  set L := Real.log (x / (4 * π)) with hL'
  set P := 3 / x + 1 / 2 * L + 1 / x ^ 2 + π / 4 with hP
  have hP0 : 0 ≤ P := by
    have : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_d2])
    positivity
  have hprod : -(1 / 4 * (P / (x - 6))) ≤ (t / 2 * alpha w * alpha' w).re := by
    have h1 : ‖t / 2 * alpha w * alpha' w‖ ≤ 1 / 4 * (P / (x - 6)) := by
      rw [norm_mul, norm_mul, show ‖(t / 2 : ℂ)‖ = t / 2 by
        rw [show (t / 2 : ℂ) = ((t / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]]
      calc t / 2 * ‖alpha w‖ * ‖alpha' w‖ ≤ 1 / 4 * P * (1 / (x - 6)) :=
            mul_le_mul (mul_le_mul (by linarith) hα (norm_nonneg _) (by norm_num)) hd (norm_nonneg _)
              (by positivity)
        _ = 1 / 4 * (P / (x - 6)) := by ring
    have h2 := Complex.abs_re_le_norm (t / 2 * alpha w * alpha' w)
    have h3 := neg_abs_le (t / 2 * alpha w * alpha' w).re
    linarith
  rw [Complex.add_re]
  have hPle : 1 / 4 * (P / (x - 6))
      ≤ 1 / 4 * ((3 / x + 1 / 2 * (x / 34) + 1 / x ^ 2 + π / 4) / (x - 6)) := by
    rw [hP]; gcongr
  linarith

/-- Polymath (1.11): `|γ| ≤ e^{0.02 y} (x/4π)^{-y/2}` on the region. -/
theorem norm_gamma_le {t x y : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hx : 200 ≤ x) :
    ‖gamma t x y‖ ≤ Real.exp (0.02 * y) * (x / (4 * π)) ^ (-y / 2) := by
  have hx0 : 0 < x := by linarith
  have hc : (x / 2 : ℝ) ≠ 0 := by positivity
  set g : ℝ → ℝ := fun σ => (logM t (σ + (x / 2 : ℝ) * I)).re with hg
  have hne : ∀ σ : ℝ, ((σ : ℂ) + (x / 2 : ℝ) * I) ≠ 0 ∧ ((σ : ℂ) + (x / 2 : ℝ) * I) ≠ 1 := by
    intro σ
    constructor
    · intro h; have := congrArg Complex.im h; simp at this; exact hx0.ne' this
    · intro h; have := congrArg Complex.im h; simp at this; exact hx0.ne' this
  have hγ : ‖gamma t x y‖ = Real.exp (g ((1 - y) / 2) - g ((1 + y) / 2)) := by
    unfold gamma
    rw [norm_div, sMinus_eq, sPlus_eq_conj, norm_M (hne _).1 (hne _).2]
    have h2 := hne ((1 + y) / 2)
    have h2' : (starRingEnd ℂ) ((((1 + y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I) ≠ 0 :=
      (map_ne_zero _).mpr h2.1
    have h2'' : (starRingEnd ℂ) ((((1 + y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I) ≠ 1 := by
      intro h
      apply h2.2
      have := congrArg (starRingEnd ℂ) h
      rwa [Complex.conj_conj, map_one] at this
    rw [norm_M h2' h2'', logM_conj_re (by simpa using hc), ← Real.exp_sub]
  rw [hγ]
  have hrpow : (x / (4 * π)) ^ (-y / 2) = Real.exp (Real.log (x / (4 * π)) * (-y / 2)) :=
    Real.rpow_def_of_pos (by positivity) _
  rw [hrpow, ← Real.exp_add, Real.exp_le_exp]
  rcases eq_or_lt_of_le hy0 with hy | hy
  · subst hy
    simp
  · have hab : (1 - y) / 2 < (1 + y) / 2 := by linarith
    have hderiv : ∀ σ : ℝ, HasDerivAt g
        (t / 2 * alpha (σ + (x / 2 : ℝ) * I) * alpha' (σ + (x / 2 : ℝ) * I)
          + alpha (σ + (x / 2 : ℝ) * I)).re σ :=
      fun σ => hasDerivAt_logM_re_horizontal hc σ
    obtain ⟨σ, hσ, hσ'⟩ := exists_hasDerivAt_eq_slope g _ hab
      (fun σ _ => (hderiv σ).continuousAt.continuousWithinAt) (fun σ _ => hderiv σ)
    have hσ0 : 0 ≤ σ := by linarith [hσ.1]
    have hσ1 : σ ≤ 1 := by linarith [hσ.2]
    have hbound := re_deriv_logM_ge ht0 ht hσ0 hσ1 hx
    rw [hσ'] at hbound
    have hy' : (1 + y) / 2 - (1 - y) / 2 = y := by ring
    rw [hy', le_div_iff₀ hy] at hbound
    nlinarith

/-! ### The fully explicit error bound -/

/-- The lower bound for `Re s_*` of `re_sStar_ge`. -/
@[expose] noncomputable def reSStarLower (t x y : ℝ) : ℝ :=
  (1 + y) / 2 + t / 4 * Real.log (x / (4 * π)) - t / 2 * (max (1 - 3 * y) 0 / x ^ 2)

/-- `errAB` with `|γ|`, `|κ|` and `Re s_*` replaced by their explicit bounds; this is the
quantity a certificate evaluates. -/
@[expose] noncomputable def errABExplicit (t x y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 (cutoff t x),
    (1 + Real.exp (0.02 * y) * (x / (4 * π)) ^ (-y / 2) *
        (cutoff t x : ℝ) ^ (t * y / (2 * (x - 6))) * (n : ℝ) ^ y) *
      b t n / (n : ℝ) ^ reSStarLower t x y *
      (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66)) - 1)

theorem one_le_cutoff {t x : ℝ} (ht : 0 ≤ t) (hx : 200 ≤ x) : 1 ≤ cutoff t x := by
  unfold cutoff
  rw [Nat.one_le_floor_iff, Real.le_sqrt (by norm_num) (by positivity), one_pow]
  have hpi := Real.pi_lt_d2
  have h1 : 1 ≤ x / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h2 : 0 ≤ t / 16 := by positivity
  linarith

theorem errAB_le_errABExplicit {t x y : ℝ} (hr : InRegion t x y) :
    errAB t x y ≤ errABExplicit t x y := by
  obtain ⟨ht0, ht, hy0, hy1, hx⟩ := hr
  have hx0 : 0 < x := by linarith
  have hN : (1 : ℝ) ≤ cutoff t x := by exact_mod_cast one_le_cutoff ht0 hx
  unfold errAB errABExplicit
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hexp : 0 ≤ Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626)
      / (x - 6.66)) - 1 := by
    rw [sub_nonneg, Real.one_le_exp_iff]
    apply div_nonneg (by positivity) (by linarith)
  have hb : 0 ≤ b t n := (Real.exp_pos _).le
  have hγ := norm_gamma_le ht0 ht hy0 hy1 hx
  have hκ := norm_kappa_le (x := x) ht0 hy0 (by linarith)
  have hNκ : (cutoff t x : ℝ) ^ ‖kappa t x y‖ ≤ (cutoff t x : ℝ) ^ (t * y / (2 * (x - 6))) :=
    Real.rpow_le_rpow_of_exponent_le hN hκ
  have hs := re_sStar_ge (x := x) ht0 (by linarith) hy0
  have hpow : (n : ℝ) ^ reSStarLower t x y ≤ (n : ℝ) ^ (sStar t x y).re :=
    Real.rpow_le_rpow_of_exponent_le hn1 hs
  have hny : 0 ≤ (n : ℝ) ^ y := by positivity
  have h1 : 1 + ‖gamma t x y‖ * (cutoff t x : ℝ) ^ ‖kappa t x y‖ * (n : ℝ) ^ y
      ≤ 1 + Real.exp (0.02 * y) * (x / (4 * π)) ^ (-y / 2) *
          (cutoff t x : ℝ) ^ (t * y / (2 * (x - 6))) * (n : ℝ) ^ y := by
    gcongr
  have hpos : 0 < (n : ℝ) ^ reSStarLower t x y := by positivity
  calc (1 + ‖gamma t x y‖ * (cutoff t x : ℝ) ^ ‖kappa t x y‖ * (n : ℝ) ^ y) * b t n
        / (n : ℝ) ^ (sStar t x y).re * _
      ≤ (1 + Real.exp (0.02 * y) * (x / (4 * π)) ^ (-y / 2) *
          (cutoff t x : ℝ) ^ (t * y / (2 * (x - 6))) * (n : ℝ) ^ y) * b t n
        / (n : ℝ) ^ reSStarLower t x y * _ := by
        gcongr
    _ = _ := rfl

/-- The nonvanishing test in the form a certificate checks: every quantity in
`errABExplicit t x y + errC0 t x y` is an explicit real function of `(t, x, y)`. -/
theorem H_ne_zero_of_lt_norm_f' {K : ℝ} (happrox : EffectiveApproximationWith K) {t x y : ℝ}
    (hr : InRegion t x y) (hf : errABExplicit t x y + K * errC0 t x y < ‖f t x y‖) :
    H t (x + y * I) ≠ 0 :=
  H_ne_zero_of_lt_norm_f happrox hr (by linarith [errAB_le_errABExplicit hr])

end DeBruijnNewman
