/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.RiemannSiegel.Integral
public import LemmaLib.Analysis.SpecialFunctions.Gamma.ComplexScale
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Riemann–Siegel integral as `ζ(s)` minus a Gaussian integral

For `Re s > 1` and `0 < c < 1`, the Riemann–Siegel integral `R(s, c)` (`RiemannSiegel.rsIntegral`)
satisfies
`R(s, c) = ζ(s) - ω^s (2π)^s / Γ(s) * ∫₀^∞ y^{s-1} e^{-πy²} / (e^{πωy} - e^{-πωy}) dy`
(`RiemannSiegel.rsIntegral_eq_zeta_sub`), where `ω = e^{iπ/4}`.

The proof is Siegel's: write `w^{-s} = (ω^s / Γ(s)) ∫₀^∞ r^{s-1} e^{-ω w r} dr` on the line (the
Gamma integral with the complex scaling `ω w`, whose real part is positive there), exchange the
integrals, and recognise the inner integral as the Mordell integral `mordell 1 z c` with
`z = i ω r / (2π)`, whose closed form (`Complex.mordell_one`) splits into a geometric series giving
`ζ(s)` and the Gaussian remainder.
-/

public section

open Complex Real Set Filter Topology MeasureTheory

local notation "ω" => Complex.rsOmega

namespace RiemannSiegel

/-! ### Powers of products -/

theorem arg_rsOmega : arg ω = π / 4 := by
  unfold Complex.rsOmega
  rw [show (π : ℂ) * I / 4 = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I (θ := π / 4)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem arg_conj_rsOmega : arg ((starRingEnd ℂ) ω) = -(π / 4) := by
  rw [Complex.arg_conj, arg_rsOmega, if_neg]
  linarith [Real.pi_pos]

theorem mul_cpow_of_arg_add_mem {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : arg x + arg y ∈ Ioc (-π) π) (r : ℂ) : (x * y) ^ r = x ^ r * y ^ r := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx hy), Complex.cpow_def_of_ne_zero hx,
    Complex.cpow_def_of_ne_zero hy, (Complex.log_mul_eq_add_log_iff hx hy).2 h, add_mul,
    Complex.exp_add]

/-- `w^{-s} = ω^s (ω w)^{-s}` when `Re (ω w) > 0`. -/
theorem cpow_neg_eq_rsOmega_cpow_mul {w s : ℂ} (hw : 0 < (ω * w).re) :
    w ^ (-s) = ω ^ s * (ω * w) ^ (-s) := by
  have hb : ω * w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hw0 : w ≠ 0 := right_ne_zero_of_mul hb
  have e : w = (starRingEnd ℂ) ω * (ω * w) := by
    rw [← mul_assoc, conj_rsOmega_mul, one_mul]
  have harg : |arg (ω * w)| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  rw [abs_lt] at harg
  have hc0 : (starRingEnd ℂ) ω ≠ 0 := by
    rw [map_ne_zero]; exact rsOmega_ne_zero
  conv_lhs => rw [e]
  rw [mul_cpow_of_arg_add_mem hc0 hb ⟨by rw [arg_conj_rsOmega]; linarith,
    by rw [arg_conj_rsOmega]; linarith [Real.pi_pos]⟩]
  congr 1
  have hinv : (starRingEnd ℂ) ω = ω⁻¹ := by
    rw [← mul_inv_eq_one₀ (inv_ne_zero rsOmega_ne_zero), inv_inv]; exact conj_rsOmega_mul
  rw [hinv, Complex.inv_cpow _ _ (by rw [arg_rsOmega]; linarith [Real.pi_pos]), Complex.cpow_neg,
    inv_inv]

theorem re_rsOmega_mul_line (c x : ℝ) : (ω * ((c : ℂ) - ω * x)).re = c * (Real.sqrt 2 / 2) := by
  rw [mul_sub, ← mul_assoc, ← sq, rsOmega_sq, rsOmega_eq]
  simp [mul_comm]

/-- The Gamma-integral representation of `w^{-s}` on the Riemann–Siegel line. -/
theorem cpow_neg_line_eq_integral {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ((c : ℂ) - ω * x) ^ (-s) = ω ^ s / Complex.Gamma s *
      ∫ r : ℝ in Ioi 0, (r : ℂ) ^ (s - 1) * cexp (-(ω * ((c : ℂ) - ω * x) * r)) := by
  have hre : 0 < (ω * ((c : ℂ) - ω * x)).re := by rw [re_rsOmega_mul_line]; positivity
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs hre,
    cpow_neg_eq_rsOmega_cpow_mul hre]
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  field_simp

/-! ### Exchanging the integrals -/

/-- The Mordell parameter `z_r = i ω r / (2π)`, for which `e^{-ω w r} = e^{2π i w z_r}`. -/
@[expose] noncomputable def mordellParam (r : ℝ) : ℂ := I * ω * r / (2 * π)

theorem exp_neg_rsOmega_mul_eq (w : ℂ) (r : ℝ) :
    cexp (-(ω * w * r)) = cexp (2 * π * I * w * mordellParam r) := by
  congr 1
  unfold mordellParam
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  rw [I_sq]
  ring

theorem exp_mul_kernel_eq_mordellIntegrand (r : ℝ) (u : ℂ) :
    cexp (-(ω * u * r)) * kernel u = mordellIntegrand 1 (mordellParam r) u := by
  rw [exp_neg_rsOmega_mul_eq]
  unfold kernel mordellIntegrand mordellExponent
  rw [mul_div_assoc', ← Complex.exp_add]
  congr 2
  ring

theorem continuous_kernel_line {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) :
    Continuous fun x : ℝ => kernel (c - ω * x) := by
  simp_rw [kernel_eq_mordellIntegrand]
  exact continuous_mordellIntegrand_line hc

theorem integrable_kernel_line {c : ℝ} (hc : ∀ n : ℤ, c ≠ n) :
    Integrable fun x : ℝ => kernel (c - ω * x) := by
  simp_rw [kernel_eq_mordellIntegrand]
  exact integrable_mordellIntegrand_line (by simp) hc

/-- The double integrand of Siegel's exchange is integrable on `ℝ × (0, ∞)`. -/
theorem integrable_uncurry_mellin {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ n : ℤ, c ≠ n) :
    Integrable (Function.uncurry fun (x r : ℝ) =>
        (r : ℂ) ^ (s - 1) * (-ω * (cexp (-(ω * ((c : ℂ) - ω * x) * r)) * kernel (c - ω * x))))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hβ : 0 < c * (Real.sqrt 2 / 2) := by positivity
  set G : ℝ × ℝ → ℝ := fun p => ‖kernel (c - ω * p.1)‖ *
    (p.2 ^ (s.re - 1) * Real.exp (-(c * (Real.sqrt 2 / 2)) * p.2)) with hG
  have hGint : Integrable G (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (integrable_kernel_line hc).norm.mul_prod
      (Complex.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hβ)
  have hprod : (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict ((univ : Set ℝ) ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  refine hGint.mono' ?_ ?_
  · rw [hprod]
    refine ContinuousOn.aestronglyMeasurable ?_ (MeasurableSet.univ.prod measurableSet_Ioi)
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_of_forall_continuousAt fun p hp => ?_
      have h2 : (0 : ℝ) < p.2 := hp.2
      exact ContinuousAt.comp (g := fun r : ℝ => (r : ℂ) ^ (s - 1))
        (continuousAt_ofReal_cpow_const _ _ (Or.inr h2.ne')) continuous_snd.continuousAt
    · refine Continuous.continuousOn ?_
      refine continuous_const.mul (Continuous.mul (by fun_prop) ?_)
      exact (continuous_kernel_line hc).comp continuous_fst
  · rw [hprod]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioi)] with p hp
    have h2 : (0 : ℝ) < p.2 := hp.2
    obtain ⟨x, r⟩ := p
    simp only [Function.uncurry_apply_pair, hG] at h2 ⊢
    rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_rsOmega, one_mul,
      norm_cpow_eq_rpow_re_of_pos h2, Complex.norm_exp, sub_re, one_re]
    have e : (-(ω * ((c : ℂ) - ω * x) * r)).re = -(c * (Real.sqrt 2 / 2)) * r := by
      rw [neg_re, Complex.re_mul_ofReal, re_rsOmega_mul_line]; ring
    rw [e]
    exact le_of_eq (by ring)

/-- Siegel's exchange: `R(s, c) = (ω^s / Γ(s)) ∫₀^∞ r^{s-1} mordell 1 (z_r) c dr`. -/
theorem rsIntegral_eq_integral_mordell {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ n : ℤ, c ≠ n) :
    rsIntegral s c = ω ^ s / Complex.Gamma s *
      ∫ r : ℝ in Ioi 0, (r : ℂ) ^ (s - 1) * mordell 1 (mordellParam r) c := by
  unfold rsIntegral integrand
  have e1 : ∀ x : ℝ, -ω * (((c : ℂ) - ω * x) ^ (-s) * kernel (c - ω * x)) =
      ω ^ s / Complex.Gamma s * ∫ r : ℝ in Ioi 0,
        (r : ℂ) ^ (s - 1) * (-ω * (cexp (-(ω * ((c : ℂ) - ω * x) * r)) * kernel (c - ω * x))) := by
    intro x
    rw [cpow_neg_line_eq_integral hs hc0 x]
    simp_rw [show ∀ r : ℝ, (r : ℂ) ^ (s - 1) *
        (-ω * (cexp (-(ω * ((c : ℂ) - ω * x) * r)) * kernel (c - ω * x))) =
        (-ω * kernel (c - ω * x)) * ((r : ℂ) ^ (s - 1) * cexp (-(ω * ((c : ℂ) - ω * x) * r)))
      from fun r => by ring]
    rw [integral_const_mul]
    ring
  simp_rw [e1]
  rw [integral_const_mul, integral_integral_swap (integrable_uncurry_mellin hs hc0 hc)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [integral_const_mul]
  congr 1
  unfold mordell
  congr 1
  ext x
  rw [exp_mul_kernel_eq_mordellIntegrand]

/-! ### The closed form of the Mordell integral at the parameter `z_r` -/

/-- The geometric part `e^{-ωr} / (1 - e^{-ωr})` of the Mordell integral at `z_r`. -/
@[expose] noncomputable def geomTerm (r : ℝ) : ℂ := cexp (-(ω * r)) / (1 - cexp (-(ω * r)))

/-- The Gaussian part `e^{-r²/(4π)} / (e^{ωr/2} - e^{-ωr/2})` of the Mordell integral at `z_r`. -/
@[expose] noncomputable def gaussTerm (r : ℝ) : ℂ :=
  cexp (-(r ^ 2 / (4 * π))) / (cexp (ω * r / 2) - cexp (-(ω * r / 2)))

theorem re_rsOmega_mul_ofReal (r : ℝ) : (ω * r).re = Real.sqrt 2 / 2 * r := by
  rw [Complex.re_mul_ofReal, rsOmega_eq]; simp

theorem norm_exp_neg_rsOmega_mul (r : ℝ) :
    ‖cexp (-(ω * r))‖ = Real.exp (-(Real.sqrt 2 / 2 * r)) := by
  rw [Complex.norm_exp, neg_re, re_rsOmega_mul_ofReal]

theorem norm_exp_neg_rsOmega_mul_lt_one {r : ℝ} (hr : 0 < r) : ‖cexp (-(ω * r))‖ < 1 := by
  rw [norm_exp_neg_rsOmega_mul, Real.exp_lt_one_iff]
  have : 0 < Real.sqrt 2 := by positivity
  nlinarith

theorem exp_neg_rsOmega_mul_ne_one {r : ℝ} (hr : 0 < r) : cexp (-(ω * r)) ≠ 1 := by
  intro h
  have := norm_exp_neg_rsOmega_mul_lt_one hr
  rw [h, norm_one] at this
  exact lt_irrefl _ this

theorem two_pi_I_mul_mordellParam (r : ℝ) : 2 * π * I * mordellParam r = -(ω * r) := by
  unfold mordellParam
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  rw [I_sq]
  ring

theorem mordellParam_exponent (r : ℝ) :
    -(π * I * mordellParam r ^ 2) + π * I * mordellParam r = -(r ^ 2 / (4 * π)) + -(ω * r / 2) := by
  unfold mordellParam
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination (-4 * I * ω ^ 2 * r ^ 2 + 4 * r ^ 2 + 8 * π * ω * r) * I_sq +
    (4 * I * r ^ 2) * rsOmega_sq

theorem mordell_mordellParam {r : ℝ} (hr : 0 < r) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    mordell 1 (mordellParam r) c = geomTerm r - gaussTerm r := by
  have hz : cexp (2 * π * I * mordellParam r) ≠ 1 := by
    rw [two_pi_I_mul_mordellParam]; exact exp_neg_rsOmega_mul_ne_one hr
  rw [Complex.mordell_one hc0 hc1 hz, two_pi_I_mul_mordellParam, mordellParam_exponent,
    Complex.exp_add]
  unfold geomTerm gaussTerm
  have h1 : 1 - cexp (-(ω * r)) ≠ 0 := sub_ne_zero.2 (exp_neg_rsOmega_mul_ne_one hr).symm
  have h2 : cexp (ω * r / 2) - cexp (-(ω * r / 2)) ≠ 0 := by
    have e : cexp (ω * r / 2) - cexp (-(ω * r / 2)) = cexp (ω * r / 2) * (1 - cexp (-(ω * r))) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    rw [e]
    exact mul_ne_zero (Complex.exp_ne_zero _) h1
  have h3 : cexp (ω * r / 2) - cexp (-(ω * r / 2)) = cexp (ω * r / 2) * (1 - cexp (-(ω * r))) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [sub_div, h3]
  congr 1
  have hBC : cexp (-(ω * r / 2)) * cexp (ω * r / 2) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [eq_div_iff (mul_ne_zero (Complex.exp_ne_zero _) h1)]
  calc cexp (-(r ^ 2 / (4 * π))) * cexp (-(ω * r / 2)) / (1 - cexp (-(ω * r))) *
        (cexp (ω * r / 2) * (1 - cexp (-(ω * r))))
      = cexp (-(r ^ 2 / (4 * π))) * (cexp (-(ω * r / 2)) * cexp (ω * r / 2)) *
        ((1 - cexp (-(ω * r))) / (1 - cexp (-(ω * r)))) := by ring
    _ = cexp (-(r ^ 2 / (4 * π))) := by rw [hBC, div_self h1, mul_one, mul_one]

/-! ### The geometric series and `ζ(s)` -/

theorem geomTerm_eq_tsum {r : ℝ} (hr : 0 < r) :
    geomTerm r = ∑' k : ℕ, cexp (-(((k : ℂ) + 1) * ω * r)) := by
  unfold geomTerm
  rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one (norm_exp_neg_rsOmega_mul_lt_one hr),
    ← tsum_mul_left]
  congr 1
  ext k
  rw [← pow_succ', ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem re_nat_add_one_mul_rsOmega (k : ℕ) : 0 < (((k : ℂ) + 1) * ω).re := by
  rw [show ((k : ℂ) + 1) * ω = ω * (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    re_rsOmega_mul_ofReal]
  positivity

theorem integrableOn_cpow_mul_geomSummand {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r))) (Ioi 0) :=
  Complex.integrableOn_cpow_mul_exp_neg_mul hs (re_nat_add_one_mul_rsOmega k)

theorem integral_norm_cpow_mul_geomSummand {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), ‖(r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r))‖ =
      (1 / (Real.sqrt 2 / 2)) ^ s.re * ((((k : ℝ) + 1) ^ s.re)⁻¹ * Real.Gamma s.re) := by
  have hβ : 0 < ((k : ℝ) + 1) * (Real.sqrt 2 / 2) := by positivity
  have e : ∀ r ∈ Ioi (0 : ℝ), ‖(r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r))‖ =
      r ^ (s.re - 1) * Real.exp (-(((k : ℝ) + 1) * (Real.sqrt 2 / 2) * r)) := by
    intro r hr
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_exp, sub_re, one_re]
    congr 2
    rw [neg_re, show ((k : ℂ) + 1) * ω * r = ω * ((((k : ℝ) + 1) * r : ℝ) : ℂ) by push_cast; ring,
      re_rsOmega_mul_ofReal]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, Real.integral_rpow_mul_exp_neg_mul_Ioi hs hβ,
    show 1 / (((k : ℝ) + 1) * (Real.sqrt 2 / 2)) = 1 / (Real.sqrt 2 / 2) * ((k : ℝ) + 1)⁻¹ by
      field_simp,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity)]
  ring

theorem summable_integral_norm_cpow_mul_geomSummand {s : ℂ} (hs : 1 < s.re) :
    Summable fun k : ℕ =>
      ∫ r in Ioi (0 : ℝ), ‖(r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r))‖ := by
  simp_rw [integral_norm_cpow_mul_geomSummand (by linarith : 0 < s.re)]
  refine Summable.mul_left _ (Summable.mul_right _ ?_)
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 hs)
  simpa using this

theorem integral_cpow_mul_geomSummand {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r)) =
      ω ^ (-s) * Complex.Gamma s * (1 / ((k : ℂ) + 1) ^ s) := by
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs (re_nat_add_one_mul_rsOmega k)]
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have harg : arg ((k : ℂ) + 1) = 0 := by
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_arg]
  rw [mul_cpow_of_arg_add_mem hk rsOmega_ne_zero
    ⟨by rw [harg, arg_rsOmega]; linarith [Real.pi_pos], by rw [harg, arg_rsOmega]; linarith [Real.pi_pos]⟩,
    Complex.cpow_neg ((k : ℂ) + 1), one_div]
  ring

/-- `∫₀^∞ r^{s-1} e^{-ωr} / (1 - e^{-ωr}) dr = ω^{-s} Γ(s) ζ(s)` for `Re s > 1`. -/
theorem integral_cpow_mul_geomTerm {s : ℂ} (hs : 1 < s.re) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * geomTerm r =
      ω ^ (-s) * Complex.Gamma s * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have e : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * geomTerm r =
      ∑' k : ℕ, (r : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * ω * r)) := by
    intro r hr
    rw [geomTerm_eq_tsum hr, tsum_mul_left]
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    ← integral_tsum_of_summable_integral_norm (integrableOn_cpow_mul_geomSummand hs0)
      (summable_integral_norm_cpow_mul_geomSummand hs)]
  simp_rw [integral_cpow_mul_geomSummand hs0]
  rw [tsum_mul_left, zeta_eq_tsum_one_div_nat_add_one_cpow hs]

end RiemannSiegel
