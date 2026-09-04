/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.EffectiveModel
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Estimates for `α` and for the prefactor of `e_{C,0}`

This file proves the estimates on `alpha` used in Section 6 of Polymath, *Effective approximation
of heat flow evolution of the Riemann ξ function*:

* on the imaginary axis, `α(iT) = ½ log (T/2π) + iπ/4 + O_≤(3/(2T))` (`norm_alpha_axis_sub_le`);
* for `0 ≤ σ ≤ 1` and `T ≥ 100`, `|Re α(σ + iT) - ½ log (T/2π)| ≤ 1/T²` and
  `0 ≤ Im α(σ + iT) ≤ π/4` (`abs_re_alpha_sub_le`, `im_alpha_mem`);
* Polymath (6.13): `|α(σ + ix/2) - log n|² ≤ ¼ log² (x/(4πn²)) + 0.667` for `1 ≤ n ≤ N`
  (`norm_alpha_sub_log_sq_le`).

It also contains two mean value bounds along complex segments (`norm_sub_le_of_hasDerivAt_segment`,
`norm_taylor_two_le`) and, as their application, the bound (6.15)–(6.17) on the logarithm of the
prefactor `exp(tπ²/64) |M₀(iT')| / |M_t(s₊)|` of the tail error `e_{C,0}` (`prefactor_log_le`).
-/

public section

open Complex Real Finset Set

namespace DeBruijnNewman

/-! ### `α` on the imaginary axis and near it -/

theorem log_axis {T : ℝ} (hT : 0 < T) :
    Complex.log (((T : ℂ) * I) / (2 * π)) = (Real.log (T / (2 * π)) : ℂ) + (π / 2 : ℝ) * I := by
  have e : ((T : ℂ) * I) / (2 * π) = ((T / (2 * π) : ℝ) : ℂ) * I := by push_cast; ring
  have hpos : 0 < T / (2 * π) := by positivity
  apply Complex.ext
  · rw [Complex.log_re, e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos]
    simp
  · rw [Complex.log_im, e, Complex.arg_real_mul _ hpos, Complex.arg_I]
    simp

theorem alpha_axis {T : ℝ} (hT : 0 < T) :
    alpha ((T : ℂ) * I) = 1 / (2 * ((T : ℂ) * I)) + 1 / ((T : ℂ) * I - 1) +
      (1 / 2 * Real.log (T / (2 * π)) : ℝ) + (π / 4 : ℝ) * I := by
  unfold alpha
  rw [log_axis hT]
  push_cast
  ring

theorem im_alpha_axis {T : ℝ} (hT : 0 < T) :
    (alpha ((T : ℂ) * I)).im = -(1 / (2 * T)) - T / (1 + T ^ 2) + π / 4 := by
  rw [alpha_axis hT]
  have h1 : (1 / (2 * ((T : ℂ) * I))).im = -(1 / (2 * T)) := by
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
  have h2 : (1 / ((T : ℂ) * I - 1)).im = -(T / (1 + T ^ 2)) := by
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    ring
  simp only [Complex.add_im, h1, h2, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
  ring

theorem re_alpha_axis {T : ℝ} (hT : 0 < T) :
    (alpha ((T : ℂ) * I)).re = -(1 / (1 + T ^ 2)) + 1 / 2 * Real.log (T / (2 * π)) := by
  rw [alpha_axis hT]
  have h1 : (1 / (2 * ((T : ℂ) * I))).re = 0 := by
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
  have h2 : (1 / ((T : ℂ) * I - 1)).re = -(1 / (1 + T ^ 2)) := by
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    ring
  simp only [Complex.add_re, h1, h2, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, sub_zero]

/-- `α(iT) = ½ log (T/2π) + iπ/4 + O_≤(3/(2T))`. -/
theorem norm_alpha_axis_sub_le {T : ℝ} (hT : 1 ≤ T) :
    ‖alpha ((T : ℂ) * I) - ((1 / 2 * Real.log (T / (2 * π)) : ℝ) + (π / 4 : ℝ) * I)‖ ≤
      3 / (2 * T) := by
  have hT0 : 0 < T := by linarith
  rw [alpha_axis hT0]
  have e : 1 / (2 * ((T : ℂ) * I)) + 1 / ((T : ℂ) * I - 1) +
      (1 / 2 * Real.log (T / (2 * π)) : ℝ) + (π / 4 : ℝ) * I -
      ((1 / 2 * Real.log (T / (2 * π)) : ℝ) + (π / 4 : ℝ) * I) =
      1 / (2 * ((T : ℂ) * I)) + 1 / ((T : ℂ) * I - 1) := by ring
  rw [e]
  have h1 : ‖1 / (2 * ((T : ℂ) * I))‖ = 1 / (2 * T) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0, mul_one]
  have h2 : ‖1 / ((T : ℂ) * I - 1)‖ ≤ 1 / T := by
    rw [norm_div, norm_one]
    have : T ≤ ‖(T : ℂ) * I - 1‖ := by
      have := Complex.abs_im_le_norm ((T : ℂ) * I - 1)
      simpa [abs_of_pos hT0] using this
    exact one_div_le_one_div_of_le hT0 this
  calc ‖1 / (2 * ((T : ℂ) * I)) + 1 / ((T : ℂ) * I - 1)‖
      ≤ ‖1 / (2 * ((T : ℂ) * I))‖ + ‖1 / ((T : ℂ) * I - 1)‖ := norm_add_le _ _
    _ ≤ 1 / (2 * T) + 1 / T := by rw [h1]; gcongr
    _ = 3 / (2 * T) := by field_simp; ring

/-- `|Re α(σ + iT) - ½ log (T/2π)| ≤ 1/T²` for `0 ≤ σ ≤ 1`, `T ≥ 1`. -/
theorem abs_re_alpha_sub_le {σ T : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    |(alpha (σ + T * I)).re - 1 / 2 * Real.log (T / (2 * π))| ≤ 1 / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  rw [re_alpha σ T hT0.ne']
  have hL : 1 / 2 * Real.log (T / (2 * π)) =
      1 / 4 * Real.log (T ^ 2) - 1 / 2 * Real.log (2 * π) := by
    rw [Real.log_div hT0.ne' (by positivity), Real.log_pow]; push_cast; ring
  rw [hL]
  have hA : 0 < σ ^ 2 + T ^ 2 := by positivity
  have hB : 0 < (σ - 1) ^ 2 + T ^ 2 := by positivity
  have h1 : 0 ≤ σ / (2 * (σ ^ 2 + T ^ 2)) := by positivity
  have h1' : σ / (2 * (σ ^ 2 + T ^ 2)) ≤ 1 / (2 * T ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg σ, sq_nonneg T]
  have h2 : (σ - 1) / ((σ - 1) ^ 2 + T ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hB.le
  have h2' : -(1 / T ^ 2) ≤ (σ - 1) / ((σ - 1) ^ 2 + T ^ 2) := by
    rw [neg_le_iff_add_nonneg', div_add_div _ _ (by positivity) hB.ne']
    apply div_nonneg _ (by positivity)
    nlinarith [sq_nonneg (σ - 1), sq_nonneg T]
  have h3 : 0 ≤ 1 / 4 * Real.log (σ ^ 2 + T ^ 2) - 1 / 4 * Real.log (T ^ 2) := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < T ^ 2) (by nlinarith : T ^ 2 ≤ σ ^ 2 + T ^ 2)
    linarith
  have h3' : 1 / 4 * Real.log (σ ^ 2 + T ^ 2) - 1 / 4 * Real.log (T ^ 2) ≤ 1 / (4 * T ^ 2) := by
    have e : Real.log (σ ^ 2 + T ^ 2) - Real.log (T ^ 2) = Real.log ((σ ^ 2 + T ^ 2) / T ^ 2) := by
      rw [Real.log_div hA.ne' (by positivity)]
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (σ ^ 2 + T ^ 2) / T ^ 2)
    have e2 : (σ ^ 2 + T ^ 2) / T ^ 2 - 1 = σ ^ 2 / T ^ 2 := by field_simp; ring
    have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
    have : σ ^ 2 / T ^ 2 ≤ 1 / T ^ 2 := by gcongr
    have e3 : 1 / (4 * T ^ 2) = 1 / 4 * (1 / T ^ 2) := by ring
    rw [e3]
    linarith
  rw [abs_le]
  constructor
  · have : 1 / (4 * T ^ 2) ≤ 1 / T ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg T])
    nlinarith
  · have : 1 / (2 * T ^ 2) + 1 / (4 * T ^ 2) ≤ 1 / T ^ 2 := by
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg T]
    nlinarith

/-- `0 ≤ Im α(σ + iT) ≤ π/4` for `0 ≤ σ ≤ 1` and `T ≥ 100`. -/
theorem im_alpha_mem {σ T : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 100 ≤ T) :
    0 ≤ (alpha (σ + T * I)).im ∧ (alpha (σ + T * I)).im ≤ π / 4 := by
  have hT0 : 0 < T := by linarith
  have hc : 3 < T := by linarith
  have h := norm_alpha_sub_alpha_le (c := T) (a := 0) (b := σ) hc hσ0
  have him := Complex.abs_im_le_norm (alpha (σ + T * I) - alpha ((0 : ℝ) + T * I))
  rw [Complex.sub_im] at him
  have h0 : alpha ((0 : ℝ) + T * I) = alpha ((T : ℂ) * I) := by simp
  rw [h0] at h him
  rw [im_alpha_axis hT0] at him
  have hb : |(alpha (σ + T * I)).im - (-(1 / (2 * T)) - T / (1 + T ^ 2) + π / 4)| ≤
      1 / (2 * T - 6) := by
    refine him.trans (h.trans ?_)
    rw [sub_zero]
    calc 1 / (2 * T - 6) * σ ≤ 1 / (2 * T - 6) * 1 := by
          gcongr; exact div_nonneg zero_le_one (by linarith)
      _ = _ := mul_one _
  rw [abs_le] at hb
  have e1 : 1 / (2 * T - 6) ≤ 1 / 194 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have e2 : 1 / (2 * T) ≤ 1 / 200 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have e3 : T / (1 + T ^ 2) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2T : 0 < 2 * T - 6 := by linarith
  have e4 : 1 / (2 * T - 6) ≤ 1 / (2 * T) + T / (1 + T ^ 2) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ h2T (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T - 100) (sq_nonneg T), sq_nonneg T]
  have hpi := Real.pi_gt_three
  constructor
  · nlinarith
  · nlinarith

/-- `|log (x/(4πn²))| ≤ x/34` for `x ≥ 200` and `1 ≤ n ≤ √(x/4π + 1/32)`. -/
theorem abs_log_div_four_pi_sq_le {x : ℝ} {n : ℕ} (hx : 200 ≤ x) (hn : 1 ≤ n)
    (hnx : (n : ℝ) ^ 2 ≤ x / (4 * π) + 1 / 32) :
    |Real.log (x / (4 * π * (n : ℝ) ^ 2))| ≤ x / 34 := by
  have hx0 : 0 < x := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hpi' := Real.pi_lt_d2
  have hLup : Real.log (x / (4 * π * (n : ℝ) ^ 2)) ≤ x / 34 := by
    have : Real.log (x / (4 * π * (n : ℝ) ^ 2)) ≤ Real.log (x / (4 * π)) := by
      apply Real.log_le_log (by positivity)
      apply div_le_div_of_nonneg_left hx0.le (by positivity)
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.2 hn2)]
    linarith [log_div_four_pi_le hx]
  have hLlow : -(1 / 400) ≤ Real.log (x / (4 * π * (n : ℝ) ^ 2)) := by
    have hpos : 0 < x / (4 * π * (n : ℝ) ^ 2) := by positivity
    have h0 := Real.one_sub_inv_le_log_of_pos hpos
    rw [inv_div] at h0
    have h1 : 4 * π * (n : ℝ) ^ 2 ≤ x + π / 8 := by
      have := mul_le_mul_of_nonneg_left hnx (by positivity : (0 : ℝ) ≤ 4 * π)
      have e : 4 * π * (x / (4 * π) + 1 / 32) = x + π / 8 := by field_simp; ring
      linarith
    have : 4 * π * (n : ℝ) ^ 2 / x ≤ 1 + 1 / 400 := by
      rw [div_le_iff₀ hx0]
      linarith
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The elementary inequality behind (6.13). -/
theorem sq_half_add_le {x L ρ : ℝ} (hx : 200 ≤ x) (hLabs : |L| ≤ x / 34) (hρ : |ρ| ≤ 4 / x ^ 2) :
    (1 / 2 * L + ρ) ^ 2 ≤ 1 / 4 * L ^ 2 + 2 / 1000 := by
  have hx0 : 0 < x := by linarith
  have key : (1 / 2 * L + ρ) ^ 2 ≤ 1 / 4 * L ^ 2 + |L| * |ρ| + ρ ^ 2 := by
    have : L * ρ ≤ |L| * |ρ| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith
  have h4 : |L| * |ρ| ≤ x / 34 * (4 / x ^ 2) := mul_le_mul hLabs hρ (abs_nonneg _) (by positivity)
  have h5 : x / 34 * (4 / x ^ 2) ≤ 1 / 1000 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hρabs : |ρ| ≤ 1 / 10000 := by
    refine hρ.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h6 : ρ ^ 2 ≤ 1 / 100000000 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hρabs 2
    rw [sq_abs] at this
    norm_num at this ⊢
    linarith
  linarith

/-- Polymath (6.13): `|α(σ + ix/2) - log n|² ≤ ¼ log² (x/(4πn²)) + 0.667` for `0 ≤ σ ≤ 1`,
`x ≥ 200` and `1 ≤ n ≤ √(x/4π + 1/32)`. -/
theorem norm_alpha_sub_log_sq_le {σ x : ℝ} {n : ℕ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hx : 200 ≤ x)
    (hn : 1 ≤ n) (hnx : (n : ℝ) ^ 2 ≤ x / (4 * π) + 1 / 32) :
    ‖alpha (σ + (x / 2 : ℝ) * I) - Real.log n‖ ^ 2 ≤
      1 / 4 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 667 / 1000 := by
  have hx0 : 0 < x := by linarith
  have hT : 100 ≤ x / 2 := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi' := Real.pi_lt_d2
  rw [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  -- the imaginary part
  obtain ⟨hi0, hi1⟩ := im_alpha_mem hσ0 hσ1 hT
  have hI : (alpha (σ + (x / 2 : ℝ) * I)).im ^ 2 ≤ π ^ 2 / 16 := by
    rw [show π ^ 2 / 16 = (π / 4) ^ 2 by ring]
    exact pow_le_pow_left₀ hi0 hi1 2
  have h7 : π ^ 2 / 16 ≤ 6203 / 10000 := by
    have h := pow_le_pow_left₀ Real.pi_pos.le hpi'.le 2
    have e : (3.15 : ℝ) ^ 2 = 9.9225 := by norm_num
    rw [e] at h
    linarith only [h]
  -- the real part
  have hρ := abs_re_alpha_sub_le hσ0 hσ1 (by linarith : (1 : ℝ) ≤ x / 2)
  have hρ' : |(alpha (σ + (x / 2 : ℝ) * I)).re - 1 / 2 * Real.log (x / 2 / (2 * π))| ≤
      4 / x ^ 2 := by
    refine hρ.trans (le_of_eq ?_)
    field_simp
    norm_num
  have hL' : 1 / 2 * Real.log (x / 2 / (2 * π)) - Real.log n =
      1 / 2 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) := by
    have e : Real.log (x / (4 * π * (n : ℝ) ^ 2)) =
        Real.log (x / 2 / (2 * π)) - 2 * Real.log n := by
      rw [show x / (4 * π * (n : ℝ) ^ 2) = (x / 2 / (2 * π)) / (n : ℝ) ^ 2 by field_simp; ring,
        Real.log_div (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [e]
    ring
  have hre' : (alpha (σ + (x / 2 : ℝ) * I)).re - Real.log n =
      1 / 2 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) +
        ((alpha (σ + (x / 2 : ℝ) * I)).re - 1 / 2 * Real.log (x / 2 / (2 * π))) := by
    linarith
  rw [hre']
  have := sq_half_add_le hx (abs_log_div_four_pi_sq_le hx hn hnx) hρ'
  linarith


/-! ### Mean value bounds along complex segments -/

/-- First-order bound along the segment `z + τ h`, `τ ∈ [0, 1]`. -/
theorem norm_sub_le_of_hasDerivAt_segment {g g' : ℂ → ℂ} {z h : ℂ} {K : ℝ}
    (hg : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' (z + τ * h)) (z + τ * h))
    (hb : ∀ τ ∈ Icc (0 : ℝ) 1, ‖g' (z + τ * h)‖ ≤ K) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ‖g (z + τ * h) - g z‖ ≤ K * ‖h‖ * τ := by
  intro τ hτ
  have hf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => g (z + s * h))
      (g' (z + s * h) * h) (Icc 0 1) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => z + (s : ℂ) * h) h s := by
      have := ((hasDerivAt_id s).ofReal_comp.mul_const h).const_add z
      simpa using this
    exact ((hg s hs).comp s h1).hasDerivWithinAt
  have := norm_image_sub_le_of_norm_deriv_le_segment' (C := K * ‖h‖) hf (fun s hs => ?_) τ hτ
  · simpa using this
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb s (Ico_subset_Icc_self hs)) (norm_nonneg _)

/-- Second-order Taylor bound along the segment `z + τ h`: if `g' ` is the derivative of `g`
along the segment and `‖g' (z + τ h) - g' z‖ ≤ K τ ‖h‖`, then
`‖g (z + h) - g z - h g' z‖ ≤ K ‖h‖² / 2`. -/
theorem norm_taylor_two_le {g g' : ℂ → ℂ} {z h : ℂ} {K : ℝ}
    (hg : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' (z + τ * h)) (z + τ * h))
    (hg' : ∀ τ ∈ Icc (0 : ℝ) 1, ‖g' (z + τ * h) - g' z‖ ≤ K * (τ * ‖h‖)) :
    ‖g (z + h) - g z - h * g' z‖ ≤ K * ‖h‖ ^ 2 / 2 := by
  set φ : ℝ → ℂ := fun τ => g (z + τ * h) - g z - τ * h * g' z with hφ
  set φ' : ℝ → ℂ := fun τ => h * (g' (z + τ * h) - g' z) with hφ'
  have hd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' τ) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun s : ℝ => z + (s : ℂ) * h) h τ := by
      have := ((hasDerivAt_id τ).ofReal_comp.mul_const h).const_add z
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => g (z + (s : ℂ) * h)) (g' (z + τ * h) * h) τ :=
      (hg τ hτ).comp τ h1
    have h3 : HasDerivAt (fun s : ℝ => (s : ℂ) * h * g' z) (h * g' z) τ := by
      have := (hasDerivAt_id τ).ofReal_comp.mul_const (h * g' z)
      simpa [mul_assoc] using this
    have := (h2.sub_const (g z)).sub h3
    refine this.congr_deriv ?_
    rw [hφ']; ring
  have hcont : ContinuousOn φ (Icc 0 1) := fun τ hτ => (hd τ hτ).continuousAt.continuousWithinAt
  set B : ℝ → ℝ := fun τ => K * ‖h‖ ^ 2 * τ ^ 2 / 2 with hB
  set B' : ℝ → ℝ := fun τ => K * ‖h‖ ^ 2 * τ with hB'
  have hBd : ∀ τ, HasDerivAt B (B' τ) τ := by
    intro τ
    have := ((hasDerivAt_pow 2 τ).const_mul (K * ‖h‖ ^ 2)).div_const 2
    refine this.congr_deriv ?_
    rw [hB']; push_cast; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (fun τ hτ => (hd τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt) (by simp [hφ, hB]) hBd
    (fun τ hτ => ?_) (right_mem_Icc.2 zero_le_one)
  · simpa [hφ, hB] using key
  · rw [hφ', hB', norm_mul]
    calc ‖h‖ * ‖g' (z + τ * h) - g' z‖ ≤ ‖h‖ * (K * (τ * ‖h‖)) :=
        mul_le_mul_of_nonneg_left (hg' τ (Ico_subset_Icc_self hτ)) (norm_nonneg _)
      _ = K * ‖h‖ ^ 2 * τ := by ring


/-! ### The prefactor of `e_{C,0}` -/

/-- The imaginary part along the segment from `iT'` to `conj s₊` stays `≥ x/2`. -/
theorem seg_im_ge {t x y : ℝ} {z h : ℂ} (ht0 : 0 ≤ t)
    (hz : z = ((x / 2 + π * t / 8 : ℝ) : ℂ) * I)
    (hh : h = (((1 + y) / 2 : ℝ) : ℂ) + ((-(π * t / 8) : ℝ) : ℂ) * I) :
    ∀ τ ∈ Icc (0 : ℝ) 1, x / 2 ≤ (z + τ * h).im := by
  intro τ hτ
  have hpi := Real.pi_gt_three
  rw [hz, hh]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero, zero_mul]
  nlinarith [mul_nonneg (sub_nonneg.2 hτ.2) (mul_nonneg Real.pi_pos.le ht0)]

/-- Second-order Taylor expansion of `log M₀` along the segment from `iT'` to `conj s₊`
(Polymath (6.16)). -/
theorem prefactor_taylor {t x y : ℝ} {z h : ℂ} (ht0 : 0 ≤ t) (hx : 200 ≤ x)
    (hz : z = ((x / 2 + π * t / 8 : ℝ) : ℂ) * I)
    (hh : h = (((1 + y) / 2 : ℝ) : ℂ) + ((-(π * t / 8) : ℝ) : ℂ) * I) :
    (logM₀ z).re - (logM₀ (z + h)).re ≤ -(h * alpha z).re + 1 / (x - 6) * ‖h‖ ^ 2 / 2 := by
  have hx6 : 0 < x - 6 := by linarith
  have hseg := seg_im_ge ht0 hz hh
  have hseg_ne : ∀ τ ∈ Icc (0 : ℝ) 1, (z + τ * h).im ≠ 0 := fun τ hτ => by
    linarith [hseg τ hτ]
  have hK : ∀ τ ∈ Icc (0 : ℝ) 1, ‖alpha' (z + τ * h)‖ ≤ 1 / (x - 6) := by
    intro τ hτ
    have h3 : 3 < (z + τ * h).im := by linarith [hseg τ hτ]
    refine (norm_alpha'_le h3).trans ?_
    apply one_div_le_one_div_of_le hx6
    linarith [hseg τ hτ]
  have hα := norm_sub_le_of_hasDerivAt_segment (g := alpha) (g' := alpha') (z := z) (h := h)
    (fun τ hτ => hasDerivAt_alpha (hseg_ne τ hτ)) hK
  have hTaylor := norm_taylor_two_le (g := logM₀) (g' := alpha) (z := z) (h := h)
    (K := 1 / (x - 6)) (fun τ hτ => hasDerivAt_logM₀ (hseg_ne τ hτ)) (fun τ hτ => by
      calc _ ≤ _ := hα τ hτ
        _ = _ := by ring)
  have := Complex.abs_re_le_norm (logM₀ (z + h) - logM₀ z - h * alpha z)
  rw [Complex.sub_re, Complex.sub_re] at this
  have := (abs_le.1 this).1
  linarith

/-- The linear term of the Taylor expansion: `Re (h α(iT')) ≥ (1+y)/4 log (T'/2π) + π²t/32
- 3‖h‖/(2T')`. -/
theorem prefactor_linear {t x y : ℝ} {z h : ℂ} (hx : 200 ≤ x) (ht0 : 0 ≤ t)
    (hz : z = ((x / 2 + π * t / 8 : ℝ) : ℂ) * I)
    (hh : h = (((1 + y) / 2 : ℝ) : ℂ) + ((-(π * t / 8) : ℝ) : ℂ) * I) :
    (1 + y) / 4 * Real.log ((x / 2 + π * t / 8) / (2 * π)) + π ^ 2 * t / 32 -
      ‖h‖ * (3 / (2 * (x / 2 + π * t / 8))) ≤ (h * alpha z).re := by
  have hpi := Real.pi_gt_three
  have hT'1 : 1 ≤ x / 2 + π * t / 8 := by nlinarith
  have hαz := norm_alpha_axis_sub_le hT'1
  rw [← hz] at hαz
  set c₀ : ℂ := ((1 / 2 * Real.log ((x / 2 + π * t / 8) / (2 * π)) : ℝ) : ℂ) +
    ((π / 4 : ℝ) : ℂ) * I with hc₀
  have hc₀_re : c₀.re = 1 / 2 * Real.log ((x / 2 + π * t / 8) / (2 * π)) := by rw [hc₀]; simp
  have hc₀_im : c₀.im = π / 4 := by rw [hc₀]; simp
  have hh_re : h.re = (1 + y) / 2 := by rw [hh]; simp
  have hh_im : h.im = -(π * t / 8) := by rw [hh]; simp
  have E2 : (h * alpha z).re = (1 + y) / 4 * Real.log ((x / 2 + π * t / 8) / (2 * π)) +
      π ^ 2 * t / 32 + (h * (alpha z - c₀)).re := by
    have : h * alpha z = h * c₀ + h * (alpha z - c₀) := by ring
    rw [this, Complex.add_re, Complex.mul_re, hh_re, hh_im, hc₀_re, hc₀_im]
    ring
  have E3 : |(h * (alpha z - c₀)).re| ≤ ‖h‖ * (3 / (2 * (x / 2 + π * t / 8))) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hαz (norm_nonneg _)
  have := (abs_le.1 E3).1
  linarith

/-- `‖h‖ ≤ 1.02` and `‖h‖² ≤ 1.04` for the Taylor increment `h = (1+y)/2 - iπt/8`. -/
theorem prefactor_norm_h {t y : ℝ} {h : ℂ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hh : h = (((1 + y) / 2 : ℝ) : ℂ) + ((-(π * t / 8) : ℝ) : ℂ) * I) :
    ‖h‖ ≤ 1.02 ∧ ‖h‖ ^ 2 ≤ 1.04 := by
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have hh_re : h.re = (1 + y) / 2 := by rw [hh]; simp
  have hh_im : h.im = -(π * t / 8) := by rw [hh]; simp
  have hh2 : ‖h‖ ^ 2 ≤ 1.04 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hh_re, hh_im]
    have : π * t ≤ 3.15 * (1 / 2) := by
      apply mul_le_mul hpi'.le ht ht0 (by norm_num)
    nlinarith [mul_nonneg Real.pi_pos.le ht0]
  refine ⟨?_, hh2⟩
  have : ‖h‖ ^ 2 ≤ (1.02 : ℝ) ^ 2 := by norm_num; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 this

/-- `Re (α(conj s₊)²) ≥ ¼ log² (x/4π) - 4 log(x/4π)/x² - π²/16`. -/
theorem re_alpha_sq_ge {x y : ℝ} {w : ℂ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hx : 200 ≤ x)
    (hw : w = (((1 + y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I) :
    Real.log (x / (4 * π)) ^ 2 / 4 - 4 * Real.log (x / (4 * π)) / x ^ 2 - π ^ 2 / 16 ≤
      (alpha w ^ 2).re := by
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have hx0 : 0 < x := by linarith
  set L := Real.log (x / (4 * π)) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]; apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hσ0 : 0 ≤ (1 + y) / 2 := by linarith
  have hσ1 : (1 + y) / 2 ≤ 1 := by linarith
  obtain ⟨hai0, hai1⟩ := im_alpha_mem hσ0 hσ1 (by linarith : 100 ≤ x / 2)
  have har := abs_re_alpha_sub_le hσ0 hσ1 (by linarith : (1 : ℝ) ≤ x / 2)
  have hLeq : Real.log (x / 2 / (2 * π)) = L := by rw [hL]; congr 1; ring
  rw [hLeq] at har
  rw [← hw] at hai0 hai1 har
  rw [show alpha w ^ 2 = alpha w * alpha w from sq _, Complex.mul_re, ← sq, ← sq]
  have hai : (alpha w).im ^ 2 ≤ π ^ 2 / 16 := by
    rw [show π ^ 2 / 16 = (π / 4) ^ 2 by ring]
    exact pow_le_pow_left₀ hai0 hai1 2
  have har' : L ^ 2 / 4 - 4 * L / x ^ 2 ≤ (alpha w).re ^ 2 := by
    have hρ : |(alpha w).re - 1 / 2 * L| ≤ 4 / x ^ 2 := by
      refine har.trans (le_of_eq ?_); field_simp; norm_num
    have h1 := (abs_le.1 hρ).1
    have h2 : 4 * L / x ^ 2 = L * (4 / x ^ 2) := by ring
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 hL0, sq_nonneg ((alpha w).re - 1 / 2 * L)]
  linarith

/-- Polymath (6.15)–(6.17) in logarithmic form: with `T' = x/2 + πt/8`,
`tπ²/64 + Re log M₀(iT') - Re log M_t(s₊) ≤ -(1+y)/4 log(x/4π) - t/16 log²(x/4π)
+ 3.58/(x-6) + log(x/4π)/(2x²)`. -/
theorem prefactor_log_le {t x y : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hx : 200 ≤ x) :
    t * π ^ 2 / 64 + (logM₀ (((x / 2 + π * t / 8 : ℝ) : ℂ) * I)).re - (logM t (sPlus x y)).re ≤
      -((1 + y) / 4) * Real.log (x / (4 * π)) - t / 16 * Real.log (x / (4 * π)) ^ 2 +
        3.58 / (x - 6) + Real.log (x / (4 * π)) / (2 * x ^ 2) := by
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have hx0 : 0 < x := by linarith
  have hx6 : 0 < x - 6 := by linarith
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ((x / 2 + π * t / 8 : ℝ) : ℂ) * I := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℂ, h = (((1 + y) / 2 : ℝ) : ℂ) + ((-(π * t / 8) : ℝ) : ℂ) * I :=
    ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (((1 + y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I := ⟨_, rfl⟩
  have hzh : z + h = w := by
    rw [hz, hh, hw]; apply Complex.ext <;> simp
  rw [← hz]
  set L := Real.log (x / (4 * π)) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]; apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hT'x : x / 2 ≤ x / 2 + π * t / 8 := by nlinarith
  -- `sPlus x y = conj w`
  have hre_logM : (logM t (sPlus x y)).re = (logM t w).re := by
    rw [show sPlus x y = (starRingEnd ℂ) w from hw ▸ sPlus_eq_conj x y,
      logM_conj_re (by rw [hw]; simp; positivity)]
  rw [hre_logM]
  have E4 : (logM t w).re = t / 4 * (alpha w ^ 2).re + (logM₀ w).re := by
    unfold logM
    rw [Complex.add_re, Complex.mul_re]
    simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_div, zero_mul, sub_zero]
  rw [E4]
  have E1 := prefactor_taylor ht0 hx hz hh
  rw [hzh] at E1
  have E2 := prefactor_linear hx ht0 hz hh
  obtain ⟨hh1, hh2⟩ := prefactor_norm_h ht0 ht hy0 hy1 hh
  have E3 := re_alpha_sq_ge hy0 hy1 hx hw
  have E5 : L ≤ Real.log ((x / 2 + π * t / 8) / (2 * π)) := by
    rw [hL, show x / (4 * π) = x / 2 / (2 * π) by ring]
    apply Real.log_le_log (by positivity)
    gcongr
  have P1 : t / 4 * (L ^ 2 / 4 - 4 * L / x ^ 2 - π ^ 2 / 16) ≤ t / 4 * (alpha w ^ 2).re :=
    mul_le_mul_of_nonneg_left E3 (by positivity)
  have P3 : (1 + y) / 4 * L ≤ (1 + y) / 4 * Real.log ((x / 2 + π * t / 8) / (2 * π)) :=
    mul_le_mul_of_nonneg_left E5 (by positivity)
  have P4 : ‖h‖ * (3 / (2 * (x / 2 + π * t / 8))) ≤ 3.06 / (x - 6) := by
    calc ‖h‖ * (3 / (2 * (x / 2 + π * t / 8))) ≤ 1.02 * (3 / x) := by
          apply mul_le_mul hh1 _ (by positivity) (by norm_num)
          apply div_le_div_of_nonneg_left (by norm_num) hx0
          linarith
      _ = 3.06 / x := by ring
      _ ≤ 3.06 / (x - 6) := by
          apply div_le_div_of_nonneg_left (by norm_num) hx6
          linarith
  have P5 : 1 / (x - 6) * ‖h‖ ^ 2 / 2 ≤ 0.52 / (x - 6) := by
    have := mul_le_mul_of_nonneg_left hh2 (by positivity : (0 : ℝ) ≤ 1 / (x - 6))
    rw [show (0.52 : ℝ) / (x - 6) = 1 / (x - 6) * 1.04 / 2 by ring]
    linarith
  have P6 : t / 4 * (4 * L / x ^ 2) ≤ L / (2 * x ^ 2) := by
    have : t * L ≤ 1 / 2 * L := mul_le_mul_of_nonneg_right ht hL0
    rw [show t / 4 * (4 * L / x ^ 2) = t * L / x ^ 2 by ring,
      show L / (2 * x ^ 2) = 1 / 2 * L / x ^ 2 by ring]
    gcongr
  have P7 : (3.58 : ℝ) / (x - 6) = 3.06 / (x - 6) + 0.52 / (x - 6) := by ring
  nlinarith [P1, P3, P4, P5, P6, P7, E1, E2]

end DeBruijnNewman
