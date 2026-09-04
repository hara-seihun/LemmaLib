/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Euler–Maclaurin formula with a third-order remainder

For a three times differentiable `f : ℝ → ℂ`, integrating by parts three times on each unit
interval gives

`∑_{k=0}^{n} f k = ∫_0^n f + (f 0 + f n)/2 + (f' n - f' 0)/12 + ∑_{k<n} ∫_k^{k+1} f''' x P3 (x-k)`,

where `P3 u = (2u³ - 3u² + u)/12 = B₃(u)/6` is a multiple of the third Bernoulli polynomial
(`sum_eq_integral_add`). The remainder kernel satisfies `|P3 u| ≤ 1/120` on `[0, 1]`
(`norm_P3_le`).

This is the form of the formula that gives Stirling's approximation of `Γ` with the explicit
remainder of `LemmaLib.Analysis.SpecialFunctions.Gamma.Stirling`.
-/

public section

open Complex Real Set Filter Topology MeasureTheory intervalIntegral

namespace EulerMaclaurin

/-- `P1 u = u - 1/2`. -/
noncomputable def P1 (u : ℝ) : ℂ := (u : ℂ) - 1 / 2

/-- `P2 u = (u² - u)/2 + 1/12`; `P2' = P1` and `P2 0 = P2 1 = 1/12`. -/
noncomputable def P2 (u : ℝ) : ℂ := ((u : ℂ) ^ 2 - u) / 2 + 1 / 12

/-- `P3 u = (2u³ - 3u² + u)/12`; `P3' = P2` and `P3 0 = P3 1 = 0`. -/
noncomputable def P3 (u : ℝ) : ℂ := (2 * (u : ℂ) ^ 3 - 3 * (u : ℂ) ^ 2 + u) / 12

theorem P1_zero : P1 0 = -(1 / 2) := by simp [P1]
theorem P1_one : P1 1 = 1 / 2 := by simp [P1]; norm_num
theorem P2_zero : P2 0 = 1 / 12 := by simp [P2]
theorem P2_one : P2 1 = 1 / 12 := by simp [P2]
theorem P3_zero : P3 0 = 0 := by simp [P3]
theorem P3_one : P3 1 = 0 := by simp [P3]; norm_num

theorem hasDerivAt_ofReal_sub (k u : ℝ) :
    HasDerivAt (fun x : ℝ => ((x - k : ℝ) : ℂ)) 1 u :=
  ((hasDerivAt_id u).sub_const k).ofReal_comp

theorem hasDerivAt_P1 (k u : ℝ) : HasDerivAt (fun x : ℝ => P1 (x - k)) 1 u :=
  (hasDerivAt_ofReal_sub k u).sub_const _

theorem hasDerivAt_ofReal_sub_pow (k u : ℝ) (n : ℕ) :
    HasDerivAt (fun x : ℝ => ((x - k : ℝ) : ℂ) ^ n) (n * ((u - k : ℝ) : ℂ) ^ (n - 1)) u := by
  have := (hasDerivAt_pow n (((u - k : ℝ) : ℂ))).comp u (hasDerivAt_ofReal_sub k u)
  simpa [Function.comp_def] using this

theorem hasDerivAt_P2 (k u : ℝ) : HasDerivAt (fun x : ℝ => P2 (x - k)) (P1 (u - k)) u := by
  have h := hasDerivAt_ofReal_sub k u
  have h2 := hasDerivAt_ofReal_sub_pow k u 2
  have := ((h2.sub h).div_const 2).add_const (1 / 12 : ℂ)
  exact this.congr_deriv (by unfold P1; norm_num; ring)

theorem hasDerivAt_P3 (k u : ℝ) : HasDerivAt (fun x : ℝ => P3 (x - k)) (P2 (u - k)) u := by
  have h := hasDerivAt_ofReal_sub k u
  have h2 := hasDerivAt_ofReal_sub_pow k u 2
  have h3 := hasDerivAt_ofReal_sub_pow k u 3
  have := (((h3.const_mul 2).sub (h2.const_mul 3)).add h).div_const 12
  exact this.congr_deriv (by unfold P2; norm_num; ring)

/-- `|P3 u| ≤ 1/120` for `0 ≤ u ≤ 1`. -/
theorem norm_P3_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖P3 u‖ ≤ 1 / 120 := by
  have : P3 u = ((2 * u ^ 3 - 3 * u ^ 2 + u) / 12 : ℝ) := by simp [P3]
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  -- `2u³ - 3u² + u = 2 w (1 - 2u)` with `w = u(1-u) ∈ [0, 1/4]`, `(1 - 2u)² = 1 - 4w`
  have hw0 : 0 ≤ u * (1 - u) := mul_nonneg hu0 (by linarith)
  have hw1 : u * (1 - u) ≤ 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have key : (2 * u ^ 3 - 3 * u ^ 2 + u) ^ 2 ≤ (1 / 10) ^ 2 := by
    have h1 : (2 * u ^ 3 - 3 * u ^ 2 + u) ^ 2 = (u * (1 - u)) ^ 2 * (1 - 4 * (u * (1 - u))) := by
      ring
    rw [h1]
    nlinarith [mul_nonneg (sq_nonneg (u * (1 - u) - 1 / 6))
      (by linarith : (0 : ℝ) ≤ 4 * (u * (1 - u)) + 1 / 3)]
  have := abs_le_of_sq_le_sq' key (by norm_num)
  constructor <;> linarith [this.1, this.2]

/-- Euler–Maclaurin on a unit interval, with the third-order remainder:
`∫_k^{k+1} f = (f k + f (k+1))/2 - (f' (k+1) - f' k)/12 - ∫_k^{k+1} f''' x * P3 (x - k)`. -/
theorem integral_unit_interval {f f' f'' f''' : ℝ → ℂ} (k : ℝ)
    (hf : ∀ x ∈ Icc k (k + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc k (k + 1), HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x ∈ Icc k (k + 1), HasDerivAt f'' (f''' x) x)
    (hcont : ContinuousOn f''' (Icc k (k + 1))) :
    ∫ x in k..(k + 1), f x = (f k + f (k + 1)) / 2 - (f' (k + 1) - f' k) / 12 -
      ∫ x in k..(k + 1), f''' x * P3 (x - k) := by
  have hk : k ≤ k + 1 := by linarith
  have hI : uIcc k (k + 1) = Icc k (k + 1) := uIcc_of_le hk
  have hf_c : ContinuousOn f (Icc k (k + 1)) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf'_c : ContinuousOn f' (Icc k (k + 1)) :=
    fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hf''_c : ContinuousOn f'' (Icc k (k + 1)) :=
    fun x hx => (hf'' x hx).continuousAt.continuousWithinAt
  have hP1_c : Continuous fun x : ℝ => P1 (x - k) := by unfold P1; fun_prop
  have hP2_c : Continuous fun x : ℝ => P2 (x - k) := by unfold P2; fun_prop
  have hP3_c : Continuous fun x : ℝ => P3 (x - k) := by unfold P3; fun_prop
  -- step 1: `∫ f = f(k+1) P1 1 - f k P1 0 - ∫ f' * P1`
  have h1 : ∫ x in k..(k + 1), f x * (1 : ℂ) =
      f (k + 1) * P1 (k + 1 - k) - f k * P1 (k - k) - ∫ x in k..(k + 1), f' x * P1 (x - k) :=
    integral_mul_deriv_eq_deriv_mul (v := fun x => P1 (x - k)) (v' := fun _ => 1)
      (fun x hx => hf x (hI ▸ hx)) (fun x _ => hasDerivAt_P1 k x)
      (hf'_c.intervalIntegrable_of_Icc hk) intervalIntegrable_const
  -- step 2: `∫ f' * P1 = f'(k+1) P2 1 - f' k P2 0 - ∫ f'' * P2`
  have h2 : ∫ x in k..(k + 1), f' x * P1 (x - k) =
      f' (k + 1) * P2 (k + 1 - k) - f' k * P2 (k - k) - ∫ x in k..(k + 1), f'' x * P2 (x - k) :=
    integral_mul_deriv_eq_deriv_mul (v := fun x => P2 (x - k)) (v' := fun x => P1 (x - k))
      (fun x hx => hf' x (hI ▸ hx)) (fun x _ => hasDerivAt_P2 k x)
      (hf''_c.intervalIntegrable_of_Icc hk) (hP1_c.intervalIntegrable _ _)
  -- step 3: `∫ f'' * P2 = f''(k+1) P3 1 - f'' k P3 0 - ∫ f''' * P3`
  have h3 : ∫ x in k..(k + 1), f'' x * P2 (x - k) =
      f'' (k + 1) * P3 (k + 1 - k) - f'' k * P3 (k - k) - ∫ x in k..(k + 1), f''' x * P3 (x - k) :=
    integral_mul_deriv_eq_deriv_mul (v := fun x => P3 (x - k)) (v' := fun x => P2 (x - k))
      (fun x hx => hf'' x (hI ▸ hx)) (fun x _ => hasDerivAt_P3 k x)
      (hcont.intervalIntegrable_of_Icc hk) (hP2_c.intervalIntegrable _ _)
  simp only [add_sub_cancel_left, sub_self, P1_zero, P1_one, P2_zero, P2_one, P3_zero, P3_one,
    mul_one] at h1 h2 h3
  rw [h1, h2, h3]
  ring

/-- Euler–Maclaurin on `[0, n]`:
`∑_{k ≤ n} f k = ∫_0^n f + (f 0 + f n)/2 + (f' n - f' 0)/12 + ∑_{k<n} ∫_k^{k+1} f''' x P3 (x-k)`. -/
theorem sum_eq_integral_add {f f' f'' f''' : ℝ → ℂ} (n : ℕ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x) (hcont : Continuous f''') :
    ∑ k ∈ Finset.range (n + 1), f k = (∫ x in (0 : ℝ)..n, f x) + (f 0 + f n) / 2 +
      (f' n - f' 0) / 12 +
        ∑ k ∈ Finset.range n, ∫ x in (k : ℝ)..(k + 1 : ℕ), f''' x * P3 (x - k) := by
  have hunit : ∀ k : ℕ, ∫ x in (k : ℝ)..(k + 1 : ℕ), f x =
      (f k + f (k + 1 : ℕ)) / 2 - (f' (k + 1 : ℕ) - f' k) / 12 -
        ∫ x in (k : ℝ)..(k + 1 : ℕ), f''' x * P3 (x - k) := by
    intro k
    have := integral_unit_interval (f := f) (f' := f') (f'' := f'') (f''' := f''') (k : ℝ)
      (fun x _ => hf x) (fun x _ => hf' x) (fun x _ => hf'' x) hcont.continuousOn
    push_cast
    exact this
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hsum : ∑ k ∈ Finset.range n, ∫ x in (k : ℝ)..(k + 1 : ℕ), f x = ∫ x in (0 : ℝ)..n, f x := by
    have := sum_integral_adjacent_intervals (μ := volume) (f := f) (a := fun k : ℕ => (k : ℝ))
      (n := n)
      (fun k _ => hfc.intervalIntegrable _ _)
    simpa using this
  have hA := Finset.sum_range_succ (fun k : ℕ => f k) n
  have hB := Finset.sum_range_succ' (fun k : ℕ => f k) n
  have hC := Finset.sum_range_sub (fun k : ℕ => f' k) n
  rw [← hsum]
  simp_rw [hunit]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    Finset.sum_add_distrib, hC]
  push_cast at hA hB ⊢
  linear_combination (hA + hB) / 2

end EulerMaclaurin
