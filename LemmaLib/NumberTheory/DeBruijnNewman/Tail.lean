/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.RtnEstimate
public import LemmaLib.NumberTheory.RiemannSiegel.Formula
public import LemmaLib.NumberTheory.RiemannSiegel.Bound

/-!
# The tail of the Riemann–Siegel expansion of `H t`

This file bounds the remainder `remainder N s = s(s-1)/16 · Γ_ℝ(s) · R(s, N + 1/2)` of the
Riemann–Siegel formula on a horizontal line `Im s = T`, in terms of `‖M₀(iT)‖`:

* `norm_M₀_horizontal_le`: `‖M₀(σ + iT)‖ ≤ ‖M₀(iT)‖ exp (σ Re α(iT) + σ²/(4T - 12))` (second-order
  Taylor expansion of `log M₀` along the horizontal line, using `‖α'‖ ≤ 1/(2T - 6)`);
* `norm_prefactor_le`: Stirling, `‖s(s-1)/16 Γ_ℝ(s)‖ ≤ ‖M₀ s‖ exp (1/(6 (Im s - 0.8)))`;
* `norm_remainder_le`: `‖remainder N (σ + iT)‖ ≤ ‖M₀(iT)‖ tailK T c σ` where `c ∈ [N+1/4, N+3/4]`
  is the line used for the integral and `tailK` is an explicit Gaussian-in-`σ` majorant.
-/

public section

open Complex Real Set Filter Topology MeasureTheory RiemannSiegel

namespace DeBruijnNewman

/-! ### `M₀` along a horizontal line -/

theorem im_axis_add (T τ σ : ℝ) : ((T : ℂ) * I + τ * (σ : ℂ)).im = T := by simp

/-- Second-order Taylor bound for `log M₀` along the horizontal line `Im s = T`. -/
theorem re_logM₀_horizontal_le {T : ℝ} (hT : 3 < T) (σ : ℝ) :
    (logM₀ ((σ : ℂ) + T * I)).re ≤
      (logM₀ ((T : ℂ) * I)).re + σ * (alpha ((T : ℂ) * I)).re + σ ^ 2 / (4 * T - 12) := by
  set z : ℂ := (T : ℂ) * I with hz
  have hzim : ∀ τ : ℝ, (z + τ * (σ : ℂ)).im = T := fun τ => im_axis_add T τ σ
  have hg : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt logM₀ (alpha (z + τ * σ)) (z + τ * σ) :=
    fun τ _ => hasDerivAt_logM₀ (by rw [hzim]; linarith)
  have hα : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt alpha (alpha' (z + τ * σ)) (z + τ * σ) :=
    fun τ _ => hasDerivAt_alpha (by rw [hzim]; linarith)
  have hb : ∀ τ ∈ Icc (0 : ℝ) 1, ‖alpha' (z + τ * σ)‖ ≤ 1 / (2 * T - 6) := by
    intro τ _
    have := norm_alpha'_le (s := z + τ * σ) (by rw [hzim]; exact hT)
    rwa [hzim] at this
  have hg' := norm_sub_le_of_hasDerivAt_segment hα hb
  have key := norm_taylor_two_le hg (K := 1 / (2 * T - 6))
    (fun τ hτ => (hg' τ hτ).trans_eq (by ring))
  have hre := (Complex.re_le_norm _).trans key
  rw [sub_re, sub_re, re_ofReal_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hre
  have e : (σ : ℂ) + T * I = z + σ := by rw [hz, add_comm]
  rw [e]
  have h2 : 0 < 2 * T - 6 := by linarith
  have e2 : 1 / (2 * T - 6) * σ ^ 2 / 2 = σ ^ 2 / (4 * T - 12) := by
    rw [show 4 * T - 12 = 2 * (2 * T - 6) by ring]
    field_simp
  linarith

/-- `‖M₀(σ + iT)‖ ≤ ‖M₀(iT)‖ exp (σ Re α(iT) + σ²/(4T - 12))` for `T > 3`. -/
theorem norm_M₀_horizontal_le {T : ℝ} (hT : 3 < T) (σ : ℝ) :
    ‖M₀ ((σ : ℂ) + T * I)‖ ≤
      ‖M₀ ((T : ℂ) * I)‖ * Real.exp (σ * (alpha ((T : ℂ) * I)).re + σ ^ 2 / (4 * T - 12)) := by
  have h1 : ((σ : ℂ) + T * I).im ≠ 0 := by simp; linarith
  have h2 : ((T : ℂ) * I).im ≠ 0 := by simp; linarith
  rw [norm_M₀ (ne_zero_of_im_ne_zero h1) (ne_one_of_im_ne_zero h1),
    norm_M₀ (ne_zero_of_im_ne_zero h2) (ne_one_of_im_ne_zero h2), ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith [re_logM₀_horizontal_le hT σ])

/-! ### The prefactor `s(s-1)/16 Γ_ℝ(s)` -/

/-- Stirling: `‖s(s-1)/16 Γ_ℝ(s)‖ ≤ ‖M₀ s‖ exp (1/(6 (Im s - 0.8)))` for `Im s > 0.8`. -/
theorem norm_prefactor_le {s : ℂ} (hs : 0.8 < s.im) :
    ‖s * (s - 1) / 16 * Gammaℝ s‖ ≤ ‖M₀ s‖ * Real.exp (1 / (6 * (s.im - 0.8))) := by
  obtain ⟨E, hE, hr⟩ := exists_r₀_eq 1 hs
  have e : s * (s - 1) / 16 * Gammaℝ s = r₀ 1 s := by
    unfold r₀; rw [Gammaℝ_def]; push_cast; rw [Complex.one_cpow]; ring
  rw [e, hr, Nat.cast_one, Complex.one_cpow, mul_one, norm_mul, Complex.norm_exp]
  gcongr
  exact (Complex.re_le_norm E).trans hE

/-! ### The remainder on a horizontal line -/

/-- The majorant of `‖remainder N (σ + iT)‖ / ‖M₀(iT)‖` along the line through
`c ∈ [N + 1/4, N + 3/4]`: with `A = π - T/(4πc²)` and `B = √2 π c - (√2/2) T/c`,
`tailK T c σ = exp (1/(6(T-0.8))) √2 √(π/A) exp (σ (Re α(iT) - log c) + σ²/(4T-12))
  (2^{σ/2} exp (B²/(4A)) + (2/√3) exp (B²/(3A)) exp (σ²/(A c²)))`. -/
@[expose] noncomputable def tailK (T c σ : ℝ) : ℝ :=
  Real.exp (1 / (6 * (T - 0.8))) * (Real.sqrt 2 * Real.sqrt (π / lineA c T)) *
    Real.exp (σ * ((alpha ((T : ℂ) * I)).re - Real.log c) + σ ^ 2 / (4 * T - 12)) *
    ((2 : ℝ) ^ (σ / 2) * Real.exp (lineB c T ^ 2 / (4 * lineA c T)) +
      2 / Real.sqrt 3 * Real.exp (lineB c T ^ 2 / (3 * lineA c T)) *
        Real.exp (σ ^ 2 / (lineA c T * c ^ 2)))

theorem tailK_nonneg (T c σ : ℝ) : 0 ≤ tailK T c σ := by
  unfold tailK
  have := Real.sqrt_nonneg (π / lineA c T)
  positivity

theorem dist_int_of_mem_Icc {c : ℝ} {N : ℕ} (hc : (N : ℝ) + 1 / 4 ≤ c) (hc' : c ≤ N + 3 / 4) :
    ∀ m : ℤ, 1 / 4 ≤ |c - m| := by
  intro m
  rcases le_or_gt m N with h | h
  · have : (m : ℝ) ≤ N := by exact_mod_cast h
    exact le_trans (by linarith) (le_abs_self _)
  · have : (N : ℝ) + 1 ≤ m := by exact_mod_cast h
    exact le_trans (by linarith) (neg_le_abs _)

/-- The bound on the Riemann–Siegel integral along the line through `c ∈ [N+1/4, N+3/4]`,
valid for every real `σ`. -/
theorem norm_rsIntegral_le_tail {T c σ : ℝ} {N : ℕ} (hT : 0 ≤ T) (hc : (N : ℝ) + 1 / 4 ≤ c)
    (hc' : c ≤ N + 3 / 4) (hA : 0 < lineA c T) :
    ‖rsIntegral ((σ : ℂ) + T * I) (N + 1 / 2)‖ ≤
      Real.sqrt 2 * Real.sqrt (π / lineA c T) * Real.exp (-(σ * Real.log c)) *
        ((2 : ℝ) ^ (σ / 2) * Real.exp (lineB c T ^ 2 / (4 * lineA c T)) +
          2 / Real.sqrt 3 * Real.exp (lineB c T ^ 2 / (3 * lineA c T)) *
            Real.exp (σ ^ 2 / (lineA c T * c ^ 2))) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hc0 : 0 < c := by linarith
  have hcZ := dist_int_of_mem_Icc hc hc'
  have hre : ((σ : ℂ) + T * I).re = σ := by simp
  have him : ((σ : ℂ) + T * I).im = T := by simp
  rw [rsIntegral_eq_of_mem_Ioo _ (n := N) (c := N + 1 / 2) (c' := c) (by linarith) (by linarith)
    (by linarith) (by linarith)]
  have hcpow : c ^ (-σ) = Real.exp (-(σ * Real.log c)) := by
    rw [Real.rpow_def_of_pos hc0]; ring_nf
  have hsqrt : Real.sqrt (π / (3 / 4 * lineA c T)) = 2 / Real.sqrt 3 * Real.sqrt (π / lineA c T) := by
    rw [show π / (3 / 4 * lineA c T) = 4 / 3 * (π / lineA c T) by field_simp,
      Real.sqrt_mul (by norm_num), Real.sqrt_div' _ (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hρ : (0 : ℝ) < 1 / 4 := by norm_num
  have hs3 : 0 < 2 / Real.sqrt 3 := by positivity
  have hsq : 0 ≤ Real.sqrt (π / lineA c T) := Real.sqrt_nonneg _
  rcases le_or_gt 0 σ with hσ | hσ
  · have := norm_rsIntegral_le (s := (σ : ℂ) + T * I) (by rw [hre]; exact hσ) (by rw [him]; exact hT)
      hc0 hρ hcZ (by rw [him]; exact hA)
    rw [hre, him] at this
    refine this.trans ?_
    rw [show Real.sqrt 2 / (4 * (1 / 4)) = Real.sqrt 2 by norm_num, hcpow]
    have h0 : 0 ≤ 2 / Real.sqrt 3 * Real.exp (lineB c T ^ 2 / (3 * lineA c T)) *
        Real.exp (σ ^ 2 / (lineA c T * c ^ 2)) := by positivity
    have h1 : 0 ≤ Real.sqrt 2 * Real.sqrt (π / lineA c T) * Real.exp (-(σ * Real.log c)) := by
      positivity
    nlinarith
  · have := norm_rsIntegral_le_of_re_nonpos (s := (σ : ℂ) + T * I) (by rw [hre]; exact hσ.le)
      (by rw [him]; exact hT) hc0 hρ hcZ (by rw [him]; exact hA)
    rw [hre, him] at this
    refine this.trans ?_
    rw [show Real.sqrt 2 / (4 * (1 / 4)) = Real.sqrt 2 by norm_num, hcpow, hsqrt,
      show lineB c T ^ 2 / (4 * (3 / 4 * lineA c T)) = lineB c T ^ 2 / (3 * lineA c T) by
        congr 1; ring]
    have h0 : 0 ≤ (2 : ℝ) ^ (σ / 2) * Real.exp (lineB c T ^ 2 / (4 * lineA c T)) := by positivity
    have h1 : 0 ≤ Real.sqrt 2 * Real.sqrt (π / lineA c T) * Real.exp (-(σ * Real.log c)) := by
      positivity
    nlinarith

/-- The remainder of the Riemann–Siegel formula on the horizontal line `Im s = T`:
`‖remainder N (σ + iT)‖ ≤ ‖M₀(iT)‖ tailK T c σ`. -/
theorem norm_remainder_le {T c σ : ℝ} {N : ℕ} (hT : 3 < T) (hc : (N : ℝ) + 1 / 4 ≤ c)
    (hc' : c ≤ N + 3 / 4) (hA : 0 < lineA c T) :
    ‖remainder N ((σ : ℂ) + T * I)‖ ≤ ‖M₀ ((T : ℂ) * I)‖ * tailK T c σ := by
  unfold remainder
  rw [norm_mul]
  have him : ((σ : ℂ) + T * I).im = T := by simp
  have h1 := norm_prefactor_le (s := (σ : ℂ) + T * I) (by rw [him]; linarith)
  rw [him] at h1
  have h2 := norm_M₀_horizontal_le hT σ
  have h3 := norm_rsIntegral_le_tail (T := T) (c := c) (σ := σ) (N := N) (by linarith) hc hc' hA
  unfold tailK
  have hM : 0 ≤ ‖M₀ ((T : ℂ) * I)‖ := norm_nonneg _
  calc ‖((σ : ℂ) + T * I) * ((σ : ℂ) + T * I - 1) / 16 * Gammaℝ ((σ : ℂ) + T * I)‖ *
        ‖rsIntegral ((σ : ℂ) + T * I) (N + 1 / 2)‖
      ≤ (‖M₀ ((T : ℂ) * I)‖ * Real.exp (σ * (alpha ((T : ℂ) * I)).re + σ ^ 2 / (4 * T - 12)) *
          Real.exp (1 / (6 * (T - 0.8)))) *
        (Real.sqrt 2 * Real.sqrt (π / lineA c T) * Real.exp (-(σ * Real.log c)) *
          ((2 : ℝ) ^ (σ / 2) * Real.exp (lineB c T ^ 2 / (4 * lineA c T)) +
            2 / Real.sqrt 3 * Real.exp (lineB c T ^ 2 / (3 * lineA c T)) *
              Real.exp (σ ^ 2 / (lineA c T * c ^ 2)))) := by
        refine mul_le_mul (h1.trans ?_) h3 (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = _ := by
        rw [show σ * ((alpha ((T : ℂ) * I)).re - Real.log c) + σ ^ 2 / (4 * T - 12) =
          (σ * (alpha ((T : ℂ) * I)).re + σ ^ 2 / (4 * T - 12)) + -(σ * Real.log c) by ring]
        simp only [Real.exp_add]
        ring

end DeBruijnNewman
