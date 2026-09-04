/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.Kernel
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The theta function, `W`, and the completed zeta function

Let `ϑ x = ∑_{n ∈ ℤ} e^{-π n² x}` (Mathlib's `HurwitzZeta.evenKernel 0`). The kernel function
`W` of `LemmaLib.NumberTheory.DeBruijnNewman.Kernel` is `W u = e^u (ϑ(e^{4u}) - 1) / 2`
(`W_eq_theta`).

Two consequences of the theta functional equation `ϑ(1/x) = √x ϑ(x)` are proved here.

* Differentiating it at `x = 1` gives the boundary value `W' 0 = -1/2` (`W'_zero`); this is the
  only place where a *derivative* of the functional equation is needed.
* Unfolding Mathlib's definition of `completedRiemannZeta₀` as the Mellin transform of the modified
  kernel and substituting `x = e^{4u}` gives Riemann's representation

  `completedRiemannZeta₀ ((1 + i z) / 2) = 8 ∫₀^∞ cos(z u) W(u) du`

  (`completedRiemannZeta₀_eq_integral`), valid for every complex `z`.
-/

public section

open Real Set Filter Topology MeasureTheory HurwitzZeta

namespace DeBruijnNewman


/-- `ϑ x = ∑_{n ∈ ℤ} e^{-π n² x}` for `x > 0` (Mathlib's `evenKernel 0`). -/
noncomputable abbrev theta (x : ℝ) : ℝ := HurwitzZeta.evenKernel 0 x

lemma hasSum_theta {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℤ => Real.exp (-π * (n : ℝ) ^ 2 * x)) (theta x) := by
  have := HurwitzZeta.hasSum_int_evenKernel (0 : ℝ) hx
  simpa using this

/-- The half-sum `∑_{m ≥ 1} e^{-π m² x} = (ϑ x - 1) / 2`. -/
lemma hasSum_theta_nat {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * x))) ((theta x - 1) / 2) := by
  have h := (hasSum_theta hx).nat_add_neg
  have h2 : HasSum (fun n : ℕ => 2 * Real.exp (-π * (n : ℝ) ^ 2 * x)) (theta x + 1) := by
    convert h using 1
    · ext n; push_cast; ring_nf
    · simp
  have h3 := (hasSum_nat_add_iff' 1).mpr h2
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow two_ne_zero, mul_zero, zero_mul,
    Real.exp_zero, mul_one] at h3
  have h4 := h3.div_const 2
  have h5 : (fun n : ℕ => Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * x))) =
      fun i : ℕ => 2 * Real.exp (-π * ((i + 1 : ℕ) : ℝ) ^ 2 * x) / 2 := by
    ext n; push_cast; ring_nf
  rw [h5, show (theta x - 1) / 2 = (theta x + 1 - 2) / 2 by ring]
  exact h4

lemma W_eq_theta (u : ℝ) : W u = Real.exp u * ((theta (Real.exp (4 * u)) - 1) / 2) := by
  unfold W
  rw [← (hasSum_theta_nat (Real.exp_pos _)).tsum_eq, ← tsum_mul_left]
  congr 1
  ext n
  simp only [Wterm]
  rw [← Real.exp_add]
  ring_nf

lemma theta_eq_W {x : ℝ} (hx : 0 < x) :
    theta x = 1 + 2 * Real.exp (-(Real.log x / 4)) * W (Real.log x / 4) := by
  have := W_eq_theta (Real.log x / 4)
  rw [show 4 * (Real.log x / 4) = Real.log x by ring, Real.exp_log hx] at this
  rw [this, Real.exp_neg]
  field_simp
  ring

/-- Functional equation `ϑ (1/x) = √x ϑ x` for `x > 0`. -/
lemma theta_inv {x : ℝ} (hx : 0 < x) : theta x⁻¹ = x ^ (1 / 2 : ℝ) * theta x := by
  have := HurwitzZeta.evenKernel_functional_equation 0 x
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero, one_div] at this
  show HurwitzZeta.evenKernel 0 x⁻¹ = x ^ (1 / 2 : ℝ) * HurwitzZeta.evenKernel 0 x
  rw [this]
  have hx' : x ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp

/-- Derivative of `ϑ` at `1`, in terms of `W`. -/
lemma hasDerivAt_theta_one : HasDerivAt theta ((W' 0 - W 0) / 2) 1 := by
  have h1 : HasDerivAt (fun x : ℝ => Real.log x / 4) (1 / 4) 1 := by
    have := (Real.hasDerivAt_log one_ne_zero).div_const 4
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(Real.log x / 4))) (-(1 / 4)) 1 := by
    have := h1.neg.exp
    simpa using this
  have h3 := (hasDerivAt_W (Real.log 1 / 4)).comp 1 h1
  have h4 := (hasDerivAt_const 1 (1 : ℝ)).add ((h2.const_mul 2).mul h3)
  refine (h4.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with x hx
    exact theta_eq_W hx
  · simp; ring

lemma theta_deriv_one : (W' 0 - W 0) / 2 = -(1 / 4) * theta 1 := by
  -- differentiate ϑ (1/x) = √x ϑ x at x = 1
  have hL : HasDerivAt (fun x : ℝ => theta x⁻¹) (-((W' 0 - W 0) / 2)) 1 := by
    have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-1) 1 := by
      have := hasDerivAt_inv (x := (1:ℝ)) one_ne_zero
      simpa using this
    have h := hasDerivAt_theta_one.comp_of_eq 1 hinv (by simp)
    exact h.congr_deriv (by ring)
  have hR : HasDerivAt (fun x : ℝ => x ^ (1 / 2 : ℝ) * theta x)
      ((1 / 2) * theta 1 + (W' 0 - W 0) / 2) 1 := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ (1 / 2 : ℝ)) (1 / 2) 1 := by
      have := Real.hasDerivAt_rpow_const (x := (1:ℝ)) (p := (1 / 2 : ℝ)) (Or.inl one_ne_zero)
      simpa using this
    exact (h1.mul hasDerivAt_theta_one).congr_deriv (by simp)
  have heq : (fun x : ℝ => theta x⁻¹) =ᶠ[𝓝 1] fun x : ℝ => x ^ (1 / 2 : ℝ) * theta x := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with x hx
    exact theta_inv hx
  have := (hL.congr_of_eventuallyEq heq.symm).unique hR
  linarith

lemma theta_one_eq : theta 1 = 1 + 2 * W 0 := by
  have := theta_eq_W (zero_lt_one' ℝ)
  simpa using this

/-- The boundary value `W' 0 = -1/2`, equivalent to the derivative of the theta functional
equation at `τ = i`. -/
theorem W'_zero : W' 0 = -(1 / 2) := by
  have h1 := theta_deriv_one
  rw [theta_one_eq] at h1
  linarith



lemma f_modif_of_one_lt {x : ℝ} (hx : 1 < x) :
    (hurwitzEvenFEPair 0).f_modif x = ((theta x - 1 : ℝ) : ℂ) := by
  simp [WeakFEPair.f_modif, hurwitzEvenFEPair, indicator_of_mem (mem_Ioi.mpr hx),
    indicator_of_notMem (show x ∉ Ioo 0 1 from fun h => absurd h.2 (not_lt.mpr hx.le))]

lemma f_modif_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx : x < 1) :
    (hurwitzEvenFEPair 0).f_modif x = ((theta x - x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  simp [WeakFEPair.f_modif, hurwitzEvenFEPair, indicator_of_mem (mem_Ioo.mpr ⟨hx0, hx⟩),
    indicator_of_notMem (show x ∉ Ioi 1 from not_lt.mpr hx.le)]

lemma ofReal_exp_cpow (v : ℝ) (w : ℂ) : ((Real.exp v : ℝ) : ℂ) ^ w = Complex.exp (w * v) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos]), mul_comm]


/-- The integrand after the substitution `x = exp v`. -/
noncomputable def G (w : ℂ) (v : ℝ) : ℂ :=
  |Real.exp v| • (((Real.exp v : ℝ) : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif (Real.exp v))

lemma Λ₀_eq_integral_G (w : ℂ) : (hurwitzEvenFEPair 0).Λ₀ w = ∫ v, G w v := by
  have := integral_image_eq_integral_abs_deriv_smul (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun x : ℝ => (x : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif x)
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at this
  exact this

lemma integrable_G (w : ℂ) : Integrable (G w) := by
  have hm : MellinConvergent (hurwitzEvenFEPair 0).f_modif w :=
    ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin w).1
  have := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun x : ℝ => (x : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif x)).mp
  rw [image_univ, Real.range_exp] at this
  have h := this hm
  rwa [IntegrableOn, Measure.restrict_univ] at h

lemma G_of_pos (w : ℂ) {v : ℝ} (hv : 0 < v) :
    G w v = ((theta (Real.exp v) - 1 : ℝ) : ℂ) * Complex.exp (w * v) := by
  unfold G
  rw [f_modif_of_one_lt (Real.one_lt_exp_iff.mpr hv), abs_of_pos (Real.exp_pos v),
    ofReal_exp_cpow, Complex.real_smul, smul_eq_mul, Complex.ofReal_exp]
  have : Complex.exp (v : ℂ) * (Complex.exp ((w - 1) * v) * ((theta (Real.exp v) - 1 : ℝ) : ℂ)) =
      ((theta (Real.exp v) - 1 : ℝ) : ℂ) * (Complex.exp (v : ℂ) * Complex.exp ((w - 1) * v)) := by
    ring
  rw [this, ← Complex.exp_add]
  congr 2
  ring

lemma G_of_neg (w : ℂ) {v : ℝ} (hv : 0 < v) :
    G w (-v) = ((theta (Real.exp v) - 1 : ℝ) : ℂ) * Complex.exp ((1 / 2 - w) * v) := by
  unfold G
  have h1 : Real.exp (-v) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [f_modif_of_lt_one (Real.exp_pos _) h1, abs_of_pos (Real.exp_pos _),
    ofReal_exp_cpow, Complex.real_smul, smul_eq_mul, Complex.ofReal_exp]
  have h2 : theta (Real.exp (-v)) = Real.exp (v / 2) * theta (Real.exp v) := by
    rw [Real.exp_neg, theta_inv (Real.exp_pos v), ← Real.exp_mul]
    congr 2
    ring
  have h3 : Real.exp (-v) ^ (-(1 / 2 : ℝ)) = Real.exp (v / 2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [h2, h3]
  have h4 : ((Real.exp (v / 2) * theta (Real.exp v) - Real.exp (v / 2) : ℝ) : ℂ) =
      Complex.exp (v / 2) * ((theta (Real.exp v) - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h4]
  have h5 : Complex.exp (-v : ℝ) * (Complex.exp ((w - 1) * (-v : ℝ)) *
      (Complex.exp (v / 2) * ((theta (Real.exp v) - 1 : ℝ) : ℂ))) =
      ((theta (Real.exp v) - 1 : ℝ) : ℂ) *
        (Complex.exp (-v : ℝ) * Complex.exp ((w - 1) * (-v : ℝ)) * Complex.exp (v / 2)) := by ring
  rw [h5, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring


/-- `Λ₀ w = ∫₀^∞ (ϑ(e^v) - 1) (e^{wv} + e^{(1/2 - w) v}) dv`. -/
lemma Λ₀_eq (w : ℂ) :
    (hurwitzEvenFEPair 0).Λ₀ w =
      ∫ v in Ioi 0, ((theta (Real.exp v) - 1 : ℝ) : ℂ) *
        (Complex.exp (w * v) + Complex.exp ((1 / 2 - w) * v)) := by
  rw [Λ₀_eq_integral_G,
    ← intervalIntegral.integral_Iic_add_Ioi (integrable_G w).integrableOn (integrable_G w).integrableOn]
  have h1 : ∫ v in Iic 0, G w v = ∫ v in Ioi 0, G w (-v) := by
    have := integral_comp_neg_Iic (0:ℝ) (fun v => G w (-v))
    simp only [neg_neg, neg_zero] at this
    exact this
  rw [h1]
  have hA : IntegrableOn (fun v => G w (-v)) (Ioi 0) := (integrable_G w).comp_neg.integrableOn
  have hB : IntegrableOn (fun v => G w v) (Ioi 0) := (integrable_G w).integrableOn
  rw [← integral_add hA hB]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [G_of_neg w hv, G_of_pos w hv]
  ring

/-- Riemann's representation: `Λ₀((1 + iz)/2) = 8 ∫₀^∞ cos(zu) W(u) du`. -/
theorem completedRiemannZeta₀_eq_integral (z : ℂ) :
    completedRiemannZeta₀ ((1 + Complex.I * z) / 2) =
      8 * ∫ u : ℝ in Ioi 0, Complex.cos (z * u) * (W u : ℂ) := by
  set w : ℂ := (1 + Complex.I * z) / 2 / 2 with hw
  have h : completedRiemannZeta₀ ((1 + Complex.I * z) / 2) = (hurwitzEvenFEPair 0).Λ₀ w / 2 := rfl
  rw [h, Λ₀_eq]
  set F : ℝ → ℂ := fun v => ((theta (Real.exp v) - 1 : ℝ) : ℂ) *
    (Complex.exp (w * v) + Complex.exp ((1 / 2 - w) * v)) with hF
  have h2 := integral_comp_mul_left_Ioi F 0 (by norm_num : (0:ℝ) < 4)
  simp only [mul_zero] at h2
  have h3 : ∫ v in Ioi 0, F v = 4 * ∫ u in Ioi 0, F (4 * u) := by
    rw [h2, Complex.real_smul]; push_cast; ring
  have h4 : ∀ u : ℝ, F (4 * u) = 4 * (Complex.cos (z * u) * (W u : ℂ)) := by
    intro u
    simp only [hF]
    have e0 : theta (Real.exp (4 * u)) - 1 = 2 * Real.exp (-u) * W u := by
      rw [W_eq_theta u, Real.exp_neg]
      field_simp
    rw [e0]
    push_cast
    have e1 : Complex.exp (-(u : ℂ)) * Complex.exp (w * (4 * u)) =
        Complex.exp (z * u * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; rw [hw]; ring
    have e2 : Complex.exp (-(u : ℂ)) * Complex.exp ((1 / 2 - w) * (4 * u)) =
        Complex.exp (-(z * u) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; rw [hw]; ring
    have e3 := Complex.two_cos (z * u)
    calc 2 * Complex.exp (-(u : ℂ)) * (W u : ℂ) *
          (Complex.exp (w * (4 * u)) + Complex.exp ((1 / 2 - w) * (4 * u)))
        = 2 * (W u : ℂ) * (Complex.exp (-(u : ℂ)) * Complex.exp (w * (4 * u)) +
            Complex.exp (-(u : ℂ)) * Complex.exp ((1 / 2 - w) * (4 * u))) := by ring
      _ = 2 * (W u : ℂ) * (2 * Complex.cos (z * u)) := by rw [e1, e2, e3]
      _ = _ := by ring
  rw [h3]
  simp_rw [h4]
  rw [integral_const_mul]
  ring

end DeBruijnNewman
