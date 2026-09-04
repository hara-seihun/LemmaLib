/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.Analysis.EulerMaclaurin
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Stirling's formula for the complex Gamma function with an explicit remainder

For `z : ℂ` with `Im z ≠ 0`,

`Γ(z) = √(2π) exp ((z - 1/2) log z - z + 1/(12 z) + ρ)` with `‖ρ‖ ≤ 1 / (30 (Im z)²)`

(`exists_Gamma_eq`), and consequently

`Γ(z) = √(2π) exp ((z - 1/2) log z - z + E)` with `‖E‖ ≤ 1/(12 ‖z‖) + 1/(30 (Im z)²)`

(`exists_Gamma_eq_sqrt_two_pi_mul_exp`). Here `log` is the principal branch.

The proof applies the Euler–Maclaurin formula of `LemmaLib.Analysis.EulerMaclaurin` to
`x ↦ log (z + x)` on `[0, n]`, which expresses Euler's sequence `GammaSeq z n = n^z n! / ∏ (z + k)`
as `√(2π) exp ((z - 1/2) log z - z) exp (stirlingRest z n - logRemainder z n)` with
`stirlingRest z n → 1/(12 z)` (`GammaSeq_eq`, `tendsto_stirlingRest`) and
`‖logRemainder z n‖ ≤ 1/(30 (Im z)²)` uniformly in `n` (`norm_logRemainder_le`). Since
`GammaSeq z n → Γ(z)`, the limit of `exp (logRemainder z n)` lies in the compact set
`exp '' closedBall 0 (1/(30 (Im z)²))`, which gives `ρ` without identifying the limit of the
remainder.
-/

public section

open Complex Real Set Filter Topology MeasureTheory intervalIntegral EulerMaclaurin

namespace Complex.Stirling

section Log

variable {z : ℂ}

theorem hasDerivAt_add_ofReal (z : ℂ) (x : ℝ) : HasDerivAt (fun x : ℝ => z + (x : ℂ)) 1 x :=
  (hasDerivAt_id x).ofReal_comp.const_add z

theorem hasDerivAt_sq_add (z : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (z + x) ^ 2) (2 * (z + x)) x := by
  have := (hasDerivAt_add_ofReal z x).mul (hasDerivAt_add_ofReal z x)
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun y => by simp [sq]

variable (hz : z.im ≠ 0)
include hz

theorem add_ofReal_ne_zero (x : ℝ) : z + x ≠ 0 := fun h => hz (by simpa using congrArg Complex.im h)

theorem add_ofReal_mem_slitPlane (x : ℝ) : z + x ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inr (by simpa using hz))

theorem hasDerivAt_log_add (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.log (z + x)) ((z + x)⁻¹) x := by
  have := (hasDerivAt_add_ofReal z x).clog_real (add_ofReal_mem_slitPlane hz x)
  simpa using this

theorem hasDerivAt_inv_add (x : ℝ) :
    HasDerivAt (fun x : ℝ => (z + x)⁻¹) (-((z + x) ^ 2)⁻¹) x := by
  have := (hasDerivAt_add_ofReal z x).inv (add_ofReal_ne_zero hz x)
  exact this.congr_deriv (by ring)

theorem hasDerivAt_neg_inv_sq_add (x : ℝ) :
    HasDerivAt (fun x : ℝ => -((z + x) ^ 2)⁻¹) (2 * ((z + x) ^ 3)⁻¹) x := by
  have h := hasDerivAt_sq_add z x
  have hne := add_ofReal_ne_zero hz x
  have := (h.inv (pow_ne_zero 2 hne)).neg
  refine this.congr_deriv ?_
  field_simp

theorem hasDerivAt_antideriv_log (x : ℝ) :
    HasDerivAt (fun x : ℝ => (z + x) * Complex.log (z + x) - (z + x)) (Complex.log (z + x)) x := by
  have h := hasDerivAt_add_ofReal z x
  have := (h.mul (hasDerivAt_log_add hz x)).sub h
  refine this.congr_deriv ?_
  rw [mul_inv_cancel₀ (add_ofReal_ne_zero hz x)]
  ring

theorem integral_log_add (n : ℕ) :
    ∫ x in (0 : ℝ)..n, Complex.log (z + x) =
      (z + n) * Complex.log (z + n) - (z + n) - (z * Complex.log z - z) := by
  have hcont : Continuous fun x : ℝ => Complex.log (z + x) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_log_add hz x).continuousAt
  have := integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_antideriv_log hz x)
    (hcont.intervalIntegrable (0 : ℝ) n)
  rw [this]
  simp

/-- The Euler–Maclaurin remainder for `log (z + x)` on `[0, n]`. -/
noncomputable def logRemainder (z : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, ∫ x in (k : ℝ)..(k + 1 : ℕ), 2 * ((z + x) ^ 3)⁻¹ * P3 (x - k)

theorem sum_log_add_eq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Complex.log (z + k) =
      (z + n) * Complex.log (z + n) - (z + n) - (z * Complex.log z - z) +
        (Complex.log z + Complex.log (z + n)) / 2 + ((z + n)⁻¹ - z⁻¹) / 12 + logRemainder z n := by
  have hcont : Continuous fun x : ℝ => 2 * ((z + x) ^ 3)⁻¹ := by
    have : ∀ x : ℝ, (z + x) ^ 3 ≠ 0 := fun x => pow_ne_zero 3 (add_ofReal_ne_zero hz x)
    fun_prop (disch := exact this _)
  have := sum_eq_integral_add (f := fun x : ℝ => Complex.log (z + x)) (f' := fun x => (z + x)⁻¹)
    (f'' := fun x => -((z + x) ^ 2)⁻¹) (f''' := fun x => 2 * ((z + x) ^ 3)⁻¹) n
    (hasDerivAt_log_add hz) (hasDerivAt_inv_add hz) (hasDerivAt_neg_inv_sq_add hz) hcont
  simp only [Complex.ofReal_natCast, ofReal_zero, add_zero] at this
  rw [this, integral_log_add hz n]
  rfl

end Log

/-- The Stirling main term `√(2π) exp ((z - 1/2) log z - z)`. -/
noncomputable def stirlingMain (z : ℂ) : ℂ :=
  (Real.sqrt (2 * π) : ℂ) * Complex.exp ((z - 1 / 2) * Complex.log z - z)

/-- The part of the exponent of `GammaSeq z n / stirlingMain z` that tends to `1/(12 z)`. -/
noncomputable def stirlingRest (z : ℂ) (n : ℕ) : ℂ :=
  z - (z + n + 1 / 2) * Complex.log (1 + z / n) +
    (Real.log (Stirling.stirlingSeq n / Real.sqrt π) : ℂ) + (12 * z)⁻¹ - (12 * (z + n))⁻¹

theorem stirlingMain_ne_zero (z : ℂ) : stirlingMain z ≠ 0 := by
  unfold stirlingMain
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne')
    (Complex.exp_ne_zero _)

theorem log_stirlingSeq {n : ℕ} (hn : 0 < n) :
    Real.log (Stirling.stirlingSeq n) =
      Real.log n.factorial - (Real.log 2 + Real.log n) / 2 - n * (Real.log n - 1) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  unfold Stirling.stirlingSeq
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_pow, Real.log_div hn'.ne' (Real.exp_pos 1).ne',
    Real.log_exp, Real.log_mul (by norm_num) hn'.ne']
  ring

theorem stirlingSeq_pos {n : ℕ} (hn : 0 < n) : 0 < Stirling.stirlingSeq n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  unfold Stirling.stirlingSeq
  positivity

theorem add_natCast_ne_zero {z : ℂ} (hz : z.im ≠ 0) (j : ℕ) : z + j ≠ 0 :=
  fun h => hz (by simpa using congrArg Complex.im h)

theorem log_add_natCast {z : ℂ} (hz : z.im ≠ 0) {n : ℕ} (hn : 0 < n) :
    Complex.log (z + n) = Real.log n + Complex.log (1 + z / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hne : (1 : ℂ) + z / n ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [Complex.div_im, hn'.ne'] at this
    exact hz (by simpa [hn'.ne'] using this)
  have := Complex.log_ofReal_mul hn' hne
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : ((n : ℝ) : ℂ) * (1 + z / n) = z + n := by
    push_cast
    field_simp
    ring
  rw [← h2, this]

theorem GammaSeq_eq {z : ℂ} (hz : z.im ≠ 0) {n : ℕ} (hn : 0 < n) :
    Complex.GammaSeq z n =
      stirlingMain z * Complex.exp (stirlingRest z n - logRemainder z n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  -- the left side as an exponential
  have hprod : ∏ j ∈ Finset.range (n + 1), (z + j) =
      Complex.exp (∑ j ∈ Finset.range (n + 1), Complex.log (z + j)) := by
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Complex.exp_log (add_natCast_ne_zero hz j)).symm
  have hfact : (n.factorial : ℂ) = Complex.exp (Real.log n.factorial) := by
    rw [← Complex.ofReal_exp, Real.exp_log (Nat.cast_pos.2 n.factorial_pos)]
    push_cast
    rfl
  have hL : Complex.GammaSeq z n = Complex.exp (Real.log n * z + Real.log n.factorial -
      ∑ j ∈ Finset.range (n + 1), Complex.log (z + j)) := by
    rw [Complex.GammaSeq, hprod, hfact, Complex.cpow_def_of_ne_zero hnC,
      ← Complex.exp_add, ← Complex.exp_sub]
    simp only [Complex.natCast_log]
  -- the right side as an exponential
  have hsqrt : (Real.sqrt (2 * π) : ℂ) = Complex.exp (((Real.log 2 + Real.log π) / 2 : ℝ)) := by
    rw [← Real.log_mul (by norm_num) Real.pi_pos.ne', ← Real.log_sqrt (by positivity),
      ← Complex.ofReal_exp, Real.exp_log (by positivity)]
  have hR : stirlingMain z * Complex.exp (stirlingRest z n - logRemainder z n) =
      Complex.exp ((Real.log 2 + Real.log π) / 2 + ((z - 1 / 2) * Complex.log z - z) +
        (stirlingRest z n - logRemainder z n)) := by
    rw [stirlingMain, hsqrt, ← Complex.exp_add, ← Complex.exp_add]
    push_cast
    rfl
  rw [hL, hR]
  congr 1
  -- the exponents agree
  rw [sum_log_add_eq hz n, stirlingRest, log_add_natCast hz hn,
    Real.log_div (stirlingSeq_pos hn).ne' (by positivity), Real.log_sqrt Real.pi_pos.le,
    log_stirlingSeq hn]
  push_cast
  field_simp
  ring

section Bound

/-- `G a b x = (a + x) / (b² √((a+x)² + b²))`, an antiderivative of `((a+x)² + b²)^{-3/2}`. -/
noncomputable def G (a b x : ℝ) : ℝ := (a + x) / (b ^ 2 * Real.sqrt ((a + x) ^ 2 + b ^ 2))

theorem hasDerivAt_G {a b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    HasDerivAt (G a b) (1 / Real.sqrt ((a + x) ^ 2 + b ^ 2) ^ 3) x := by
  have hpos : 0 < (a + x) ^ 2 + b ^ 2 := by positivity
  have hS : 0 < Real.sqrt ((a + x) ^ 2 + b ^ 2) := Real.sqrt_pos.2 hpos
  have hS2 := Real.sq_sqrt hpos.le
  have hu : HasDerivAt (fun y : ℝ => a + y) 1 x := (hasDerivAt_id x).const_add a
  have hin : HasDerivAt (fun y : ℝ => (a + y) ^ 2 + b ^ 2) (2 * (a + x)) x := by
    have := (hu.pow 2).add_const (b ^ 2)
    simpa using this
  have hsq := hin.sqrt hpos.ne'
  have hv := hsq.const_mul (b ^ 2)
  have := hu.div hv (by positivity)
  refine this.congr_deriv ?_
  set S := Real.sqrt ((a + x) ^ 2 + b ^ 2) with hSdef
  field_simp
  linear_combination hS2

theorem abs_G_le {a b : ℝ} (hb : b ≠ 0) (x : ℝ) : |G a b x| ≤ 1 / b ^ 2 := by
  have hpos : 0 < (a + x) ^ 2 + b ^ 2 := by positivity
  have hS : 0 < Real.sqrt ((a + x) ^ 2 + b ^ 2) := Real.sqrt_pos.2 hpos
  have hb2 : 0 < b ^ 2 := by positivity
  have habs : |a + x| ≤ Real.sqrt ((a + x) ^ 2 + b ^ 2) := Real.abs_le_sqrt (by nlinarith)
  have hden : 0 < b ^ 2 * Real.sqrt ((a + x) ^ 2 + b ^ 2) := mul_pos hb2 hS
  unfold G
  rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden hb2]
  calc |a + x| * b ^ 2 ≤ Real.sqrt ((a + x) ^ 2 + b ^ 2) * b ^ 2 := by gcongr
    _ = 1 * (b ^ 2 * Real.sqrt ((a + x) ^ 2 + b ^ 2)) := by ring

theorem norm_add_ofReal (z : ℂ) (x : ℝ) : ‖z + x‖ = Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp

theorem norm_integrand_le {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) {x : ℝ} (hx : x ∈ Icc (k : ℝ) (k + 1)) :
    ‖2 * ((z + x) ^ 3)⁻¹ * P3 (x - k)‖ ≤
      1 / 60 * (1 / Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3) := by
  rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_add_ofReal, Complex.norm_ofNat]
  have hP := norm_P3_le (u := x - k) (by linarith [hx.1]) (by linarith [hx.2])
  have hS : 0 < Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) := Real.sqrt_pos.2 (by positivity)
  calc 2 * (Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3)⁻¹ * ‖P3 (x - k)‖ ≤
      2 * (Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3)⁻¹ * (1 / 120) := by gcongr
    _ = _ := by ring

theorem norm_logRemainder_le {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) :
    ‖logRemainder z n‖ ≤ 1 / (30 * z.im ^ 2) := by
  set g : ℝ → ℝ := fun x => 1 / Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3 with hg
  have hgc : Continuous g := by
    have : ∀ x : ℝ, Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3 ≠ 0 := fun x =>
      pow_ne_zero 3 (Real.sqrt_pos.2 (by positivity)).ne'
    rw [hg]
    fun_prop (disch := exact this _)
  have hterm : ∀ k : ℕ, ‖∫ x in (k : ℝ)..(k + 1 : ℕ), 2 * ((z + x) ^ 3)⁻¹ * P3 (x - k)‖ ≤
      1 / 60 * (G z.re z.im (k + 1 : ℕ) - G z.re z.im k) := by
    intro k
    have hk : (k : ℝ) ≤ (k + 1 : ℕ) := by push_cast; linarith
    have hint : ∫ x in (k : ℝ)..(k + 1 : ℕ), 1 / 60 * g x =
        1 / 60 * (G z.re z.im (k + 1 : ℕ) - G z.re z.im k) := by
      rw [intervalIntegral.integral_const_mul,
        integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_G hz x) (hgc.intervalIntegrable _ _)]
    rw [← hint]
    refine norm_integral_le_of_norm_le hk ?_ ((hgc.const_mul _).intervalIntegrable _ _)
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx' : x ∈ Icc (k : ℝ) (k + 1) := ⟨hx.1.le, by simpa using hx.2⟩
    exact norm_integrand_le hz k hx'
  calc ‖logRemainder z n‖ ≤ ∑ k ∈ Finset.range n,
        ‖∫ x in (k : ℝ)..(k + 1 : ℕ), 2 * ((z + x) ^ 3)⁻¹ * P3 (x - k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, 1 / 60 * (G z.re z.im (k + 1 : ℕ) - G z.re z.im k) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 1 / 60 * (G z.re z.im n - G z.re z.im 0) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun k : ℕ => G z.re z.im k)]
        simp
    _ ≤ 1 / 60 * (1 / z.im ^ 2 + 1 / z.im ^ 2) := by
        gcongr
        have h1 := abs_G_le (a := z.re) hz (n : ℝ)
        have h2 := abs_G_le (a := z.re) hz 0
        rw [abs_le] at h1 h2
        linarith [h1.2, h2.1]
    _ = 1 / (30 * z.im ^ 2) := by ring

end Bound

section Limit

variable {z : ℂ}

theorem ne_zero_of_im_ne_zero' (hz : z.im ≠ 0) : z ≠ 0 := fun h => hz (by simp [h])

theorem tendsto_div_natCast : Tendsto (fun n : ℕ => z / n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have : (fun n : ℕ => ‖z / n‖) = fun n : ℕ => ‖z‖ / n := by
    ext n; rw [norm_div, Complex.norm_natCast]
  rw [this]
  exact tendsto_const_div_atTop_nhds_zero_nat _

theorem tendsto_div_natCast_nhdsNE (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => z / n) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_div_natCast (z := z), ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  exact div_ne_zero (ne_zero_of_im_ne_zero' hz) hn'

theorem tendsto_log_one_add_div :
    Tendsto (fun n : ℕ => Complex.log (1 + z / n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 + z / n) atTop (𝓝 1) := by
    simpa using (tendsto_div_natCast (z := z)).const_add 1
  have := (continuousAt_clog one_mem_slitPlane).tendsto.comp h1
  simpa [Function.comp_def] using this

theorem tendsto_inv_mul_log_one_add_div (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => (z / n)⁻¹ * Complex.log (1 + z / n)) atTop (𝓝 1) := by
  have h := (Complex.hasDerivAt_log one_mem_slitPlane).tendsto_slope_zero.comp
    (tendsto_div_natCast_nhdsNE hz)
  simpa [Function.comp_def] using h

theorem tendsto_mul_log_one_add_div (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => (z + n + 1 / 2) * Complex.log (1 + z / n)) atTop (𝓝 z) := by
  have h := ((tendsto_log_one_add_div (z := z)).const_mul (z + 1 / 2)).add
    ((tendsto_inv_mul_log_one_add_div hz).const_mul z)
  simp only [mul_zero, mul_one, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  have hz0 := ne_zero_of_im_ne_zero' hz
  field_simp
  ring

theorem tendsto_inv_add_natCast (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => (12 * (z + n))⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 12 * z * (1 + z / n)) atTop (𝓝 (12 * z * (1 + 0))) :=
    tendsto_const_nhds.mul ((tendsto_div_natCast (z := z)).const_add 1)
  have h := (tendsto_div_natCast (z := z)).div h1 (by simp [ne_zero_of_im_ne_zero' hz])
  simp only [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  have hz0 := ne_zero_of_im_ne_zero' hz
  have hzn : z + n ≠ 0 := add_natCast_ne_zero hz n
  simp only [Pi.div_apply]
  field_simp
  rw [add_comm (n : ℂ) z, div_self hzn]

theorem tendsto_log_stirlingSeq_div :
    Tendsto (fun n : ℕ => (Real.log (Stirling.stirlingSeq n / Real.sqrt π) : ℂ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => Stirling.stirlingSeq n / Real.sqrt π) atTop (𝓝 1) := by
    have := Stirling.tendsto_stirlingSeq_sqrt_pi.div_const (Real.sqrt π)
    rwa [div_self (Real.sqrt_pos.2 Real.pi_pos).ne'] at this
  have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1)
  simp only [Function.comp_def, Real.log_one] at h2
  have := (Complex.continuous_ofReal.tendsto 0).comp h2
  simpa [Function.comp_def] using this

theorem tendsto_stirlingRest (hz : z.im ≠ 0) :
    Tendsto (stirlingRest z) atTop (𝓝 ((12 * z)⁻¹)) := by
  have h := ((((tendsto_const_nhds (x := z)).sub (tendsto_mul_log_one_add_div hz)).add
    tendsto_log_stirlingSeq_div).add (tendsto_const_nhds (x := (12 * z)⁻¹))).sub
    (tendsto_inv_add_natCast hz)
  simp only [sub_self, zero_add, sub_zero] at h
  exact h

end Limit

theorem Gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Complex.Gamma z ≠ 0 :=
  Complex.Gamma_ne_zero fun m h => hz (by simp [h])

/-- Stirling's formula with an explicit remainder: for `Im z ≠ 0`,
`Γ(z) = √(2π) exp ((z - 1/2) log z - z + 1/(12 z) + ρ)` with `‖ρ‖ ≤ 1 / (30 (Im z)²)`. -/
theorem exists_Gamma_eq {z : ℂ} (hz : z.im ≠ 0) :
    ∃ ρ : ℂ, ‖ρ‖ ≤ 1 / (30 * z.im ^ 2) ∧
      Complex.Gamma z = stirlingMain z * Complex.exp ((12 * z)⁻¹ + ρ) := by
  set c : ℝ := 1 / (30 * z.im ^ 2) with hc
  set K : Set ℂ := Complex.exp '' Metric.closedBall 0 c with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 c).image Complex.continuous_exp
  have hmem : ∀ n, Complex.exp (logRemainder z n) ∈ K := fun n =>
    ⟨logRemainder z n, mem_closedBall_zero_iff.2 (norm_logRemainder_le hz n), rfl⟩
  have hΓ := Gamma_ne_zero_of_im_ne_zero hz
  set L : ℂ := stirlingMain z * Complex.exp ((12 * z)⁻¹) / Complex.Gamma z with hL
  have hlim : Tendsto (fun n => Complex.exp (logRemainder z n)) atTop (𝓝 L) := by
    have h := (tendsto_const_nhds (x := stirlingMain z).mul
      ((tendsto_stirlingRest hz).cexp)).div (Complex.GammaSeq_tendsto_Gamma z) hΓ
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Pi.div_apply]
    rw [GammaSeq_eq hz hn, Complex.exp_sub]
    have := stirlingMain_ne_zero z
    have := Complex.exp_ne_zero (stirlingRest z n)
    have := Complex.exp_ne_zero (logRemainder z n)
    field_simp
  have hLK : L ∈ K := hKc.isClosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
  obtain ⟨ρ', hρ', hρ'L⟩ := hLK
  refine ⟨-ρ', by simpa using mem_closedBall_zero_iff.1 hρ', ?_⟩
  rw [Complex.exp_add, Complex.exp_neg, hρ'L, hL]
  have := stirlingMain_ne_zero z
  field_simp

/-- Stirling's formula with an explicit remainder, for `Im z ≠ 0`:
`Γ(z) = √(2π) exp ((z - 1/2) log z - z + E)` with `‖E‖ ≤ 1/(12 ‖z‖) + 1/(30 (Im z)²)`. -/
theorem exists_Gamma_eq_sqrt_two_pi_mul_exp {z : ℂ} (hz : z.im ≠ 0) :
    ∃ E : ℂ, ‖E‖ ≤ 1 / (12 * ‖z‖) + 1 / (30 * z.im ^ 2) ∧
      Complex.Gamma z = Real.sqrt (2 * π) * Complex.exp ((z - 1 / 2) * Complex.log z - z + E) := by
  obtain ⟨ρ, hρ, hΓ⟩ := exists_Gamma_eq hz
  refine ⟨(12 * z)⁻¹ + ρ, ?_, ?_⟩
  · refine (norm_add_le _ _).trans ?_
    rw [norm_inv, norm_mul, Complex.norm_ofNat, one_div]
    exact add_le_add le_rfl hρ
  · rw [hΓ, stirlingMain, mul_assoc, ← Complex.exp_add]

end Complex.Stirling
