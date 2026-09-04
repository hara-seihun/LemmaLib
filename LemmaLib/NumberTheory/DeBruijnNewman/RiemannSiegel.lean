/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.EffectiveModel
public import LemmaLib.NumberTheory.DeBruijnNewman.Heat
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Riemann–Siegel input of the effective model

This file records the two analytic inputs of Polymath Theorem 1.3 (*Effective approximation of
heat flow evolution of the Riemann ξ function*, Res. Math. Sci. 6 (2019)) as propositions, and
the algebra that connects them to the model `B t * f t x y`. `RtnEstimate` is proved in
`LemmaLib.NumberTheory.DeBruijnNewman.RtnEstimate`; `TailEstimateWith 20` is proved in
`LemmaLib.NumberTheory.DeBruijnNewman.TailEstimate` (the constant `1` of Polymath's Proposition
6.3, `TailEstimate`, would need Arias de Reyna's explicit Riemann–Siegel remainder bounds).

* `r₀ n s` is the `n`-th term `(1/8) (s(s-1)/2) π^{-s/2} Γ(s/2) n^{-s}` of the Riemann–Siegel
  expansion of `ξ(s)/8`, and `r t n s` is its heat flow (Polymath (5.2)).
* `mainTerm t n s = M t s * b_n^t / n^{s + (t/2) α(s)}` is the approximation to `r t n s` of
  Polymath Proposition 6.1, and `epsR t n s` its relative error (6.3).
* `epsTilde t s` is the error term (6.6) of the tail of the Riemann–Siegel expansion.
* `RtnEstimate` is Proposition 6.1 (`r t n s = mainTerm t n s (1 + O_≤(epsR t n s))`), and
  `TailEstimateWith K` is the expansion (5.4) of `H t` together with the remainder bound of
  Proposition 6.3 (with the bound `|C₀(p)| ≤ 1/2` on the Riemann–Siegel kernel) weakened by
  the factor `K`; `TailEstimate` is the case `K = 1`.

The remaining results are unconditional: `B t (x + iy) * f t x y` is the sum of the main terms at
`s₊` and `s₋` (`B_mul_f`), and the main terms are compatible with complex conjugation.
-/

public section

open Complex Real Finset

namespace DeBruijnNewman

/-- `r_{0,n}(s) = (1/8) (s(s-1)/2) π^{-s/2} Γ(s/2) n^{-s}`, the `n`-th main term of the
Riemann–Siegel expansion of `ξ(s)/8`. -/
@[expose] noncomputable def r₀ (n : ℕ) (s : ℂ) : ℂ :=
  s * (s - 1) / 16 * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * (n : ℂ) ^ (-s)

/-- The heat flow of `r₀`: `r_{t,n}(s) = ∫ r_{0,n}(s + √t v) e^{-v²}/√π dv`. -/
@[expose] noncomputable def r (t : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ∫ v : ℝ, r₀ n (s + Real.sqrt t * v) * (gauss v : ℂ)

/-- The approximation `M_t(s) b_n^t / n^{s + (t/2) α(s)}` to `r_{t,n}(s)`. -/
@[expose] noncomputable def mainTerm (t : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  M t s * (b t n : ℂ) / (n : ℂ) ^ (s + t / 2 * alpha s)

/-- `ε_{t,n}(σ + iT) = exp ((t²/8 |α(σ+iT) - log n|² + t/4 + 1/6) / (T - 3.33)) - 1`
(Polymath (6.3)). -/
@[expose] noncomputable def epsR (t : ℝ) (n : ℕ) (s : ℂ) : ℝ :=
  Real.exp ((t ^ 2 / 8 * ‖alpha s - Real.log n‖ ^ 2 + t / 4 + 1 / 6) / (s.im - 3.33)) - 1

/-- `ε~(σ + iT) = (0.397 · 9^σ / (a - 0.865) + 5 / (3 (T - 6))) exp (3.49 / (T - 4))` with
`a = √((T + πt/8) / 2π)` (Polymath (6.6)). -/
@[expose] noncomputable def epsTilde (t : ℝ) (s : ℂ) : ℝ :=
  (0.397 * (9 : ℝ) ^ s.re / (Real.sqrt ((s.im + π * t / 8) / (2 * π)) - 0.865) +
    5 / (3 * (s.im - 6))) * Real.exp (3.49 / (s.im - 4))

/-- Polymath Proposition 6.1: `r_{t,n}(s) = M_t(s) b_n^t n^{-s - (t/2) α(s)} (1 + O_≤(ε_{t,n}(s)))`
for `0 ≤ t ≤ 1/2`, `n ≥ 1` and `Im s > 10`. -/
@[expose] def RtnEstimate : Prop :=
  ∀ (t : ℝ) (n : ℕ) (s : ℂ), 0 ≤ t → t ≤ 1 / 2 → 1 ≤ n → 10 < s.im →
    ‖r t n s - mainTerm t n s‖ ≤ ‖mainTerm t n s‖ * epsR t n s

/-- The Riemann–Siegel expansion of `H t` (Polymath (5.4)) together with an estimate of its
remainder: the part of `H_t(x+iy)` beyond the two sums `∑ r_{t,n}(s₋) + ∑ r_{t,n}^*(s₊)` is at
most `K` times `exp (tπ²/64) |M₀(iT')| (1 + ε~(s₋) + ε~(s₊))`, where `T' = x/2 + πt/8`. -/
@[expose] def TailEstimateWith (K : ℝ) : Prop :=
  ∀ t x y : ℝ, InRegion t x y →
    ‖H t (x + y * I) - ∑ n ∈ Icc 1 (cutoff t x), r t n (sMinus x y)
        - ∑ n ∈ Icc 1 (cutoff t x), (starRingEnd ℂ) (r t n ((starRingEnd ℂ) (sPlus x y)))‖ ≤
      K * (Real.exp (t * π ^ 2 / 64) * ‖M₀ (((x / 2 + π * t / 8 : ℝ) : ℂ) * I)‖ *
        (1 + epsTilde t (sMinus x y) + epsTilde t ((starRingEnd ℂ) (sPlus x y))))

/-- The tail estimate with the constant `1` of Polymath: the expansion (5.4) together with
Proposition 6.3 and the bound `|C₀(p)| ≤ 1/2` on the Riemann–Siegel kernel. -/
@[expose] def TailEstimate : Prop := TailEstimateWith 1


/-! ### Conjugation symmetries -/

theorem ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 := fun h => hs (by simp [h])

theorem ne_one_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 1 := fun h => hs (by simp [h])

theorem M₀_conj {s : ℂ} (hs : s.im ≠ 0) : M₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (M₀ s) := by
  have hs' : ((starRingEnd ℂ) s).im ≠ 0 := by simpa using hs
  rw [M₀_eq_exp_logM₀ (ne_zero_of_im_ne_zero hs) (ne_one_of_im_ne_zero hs),
    M₀_eq_exp_logM₀ (ne_zero_of_im_ne_zero hs') (ne_one_of_im_ne_zero hs'), logM₀_conj hs,
    ← Complex.exp_conj]

theorem M_conj (t : ℝ) {s : ℂ} (hs : s.im ≠ 0) :
    M t ((starRingEnd ℂ) s) = (starRingEnd ℂ) (M t s) := by
  unfold M
  rw [M₀_conj hs, alpha_conj hs, map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_pow, map_div₀, Complex.conj_ofReal, map_ofNat]

theorem natCast_cpow_conj (n : ℕ) (w : ℂ) :
    (n : ℂ) ^ ((starRingEnd ℂ) w) = (starRingEnd ℂ) ((n : ℂ) ^ w) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero]
    by_cases hw : w = 0
    · simp [hw]
    · rw [Complex.zero_cpow hw, Complex.zero_cpow (by simpa using hw), map_zero]
  · have harg : ((n : ℂ)).arg ≠ π := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]

theorem mainTerm_conj (t : ℝ) (n : ℕ) {s : ℂ} (hs : s.im ≠ 0) :
    mainTerm t n ((starRingEnd ℂ) s) = (starRingEnd ℂ) (mainTerm t n s) := by
  unfold mainTerm
  rw [M_conj t hs, alpha_conj hs, map_div₀, map_mul, Complex.conj_ofReal, ← natCast_cpow_conj]
  congr 2
  simp only [map_add, map_mul, map_div₀, Complex.conj_ofReal, map_ofNat]

theorem b_pos (t : ℝ) (n : ℕ) : 0 < b t n := Real.exp_pos _

theorem norm_mainTerm (t : ℝ) {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖mainTerm t n s‖ = ‖M t s‖ * b t n / (n : ℝ) ^ (s + t / 2 * alpha s).re := by
  unfold mainTerm
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast_cpow_of_pos hn,
    Real.norm_eq_abs, abs_of_pos (b_pos t n)]

/-! ### `B_t f_t` as the sum of the main terms -/

theorem conj_sPlus (x y : ℝ) :
    (starRingEnd ℂ) (sPlus x y) = (((1 + y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I := by
  unfold sPlus
  rw [sPlus_eq_conj, Complex.conj_conj]

theorem sMinus_eq' (x y : ℝ) : sMinus x y = (((1 - y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I := by
  unfold sMinus; exact sMinus_eq x y

theorem im_sMinus (x y : ℝ) : (sMinus x y).im = x / 2 := by rw [sMinus_eq']; simp

theorem re_sMinus (x y : ℝ) : (sMinus x y).re = (1 - y) / 2 := by rw [sMinus_eq']; simp

theorem im_conj_sPlus (x y : ℝ) : ((starRingEnd ℂ) (sPlus x y)).im = x / 2 := by
  rw [conj_sPlus]; simp

theorem re_conj_sPlus (x y : ℝ) : ((starRingEnd ℂ) (sPlus x y)).re = (1 + y) / 2 := by
  rw [conj_sPlus]; simp

theorem im_sPlus (x y : ℝ) : (sPlus x y).im = -(x / 2) := by
  have := im_conj_sPlus x y
  rw [Complex.conj_im] at this
  linarith

theorem conj_sPlus_eq_sMinus_add (x y : ℝ) : (starRingEnd ℂ) (sPlus x y) = sMinus x y + y := by
  rw [conj_sPlus, sMinus_eq']
  apply Complex.ext
  · simp; ring
  · simp

/-- `conj s_* + κ = s₋ + (t/2) α(s₋) + y`. -/
theorem conj_sStar_add_kappa (t x y : ℝ) (hx : x ≠ 0) :
    (starRingEnd ℂ) (sStar t x y) + kappa t x y = sMinus x y + t / 2 * alpha (sMinus x y) + y := by
  have him : (sPlus x y).im ≠ 0 := by rw [im_sPlus]; exact neg_ne_zero.mpr (by positivity)
  unfold sStar kappa
  have e1 : ((1 - y + x * I) / 2 : ℂ) = sMinus x y := rfl
  have e2 : ((1 + y + x * I) / 2 : ℂ) = (starRingEnd ℂ) (sPlus x y) := by
    rw [conj_sPlus]; apply Complex.ext <;> simp
  rw [map_add, map_mul, ← alpha_conj him, map_div₀, Complex.conj_ofReal, map_ofNat, e1, e2,
    conj_sPlus_eq_sMinus_add]
  ring

theorem B_mul_f (t x y : ℝ) (hx : x ≠ 0) :
    B t (x + y * I) * f t x y =
      ∑ n ∈ Icc 1 (cutoff t x), mainTerm t n (sPlus x y) +
        ∑ n ∈ Icc 1 (cutoff t x), mainTerm t n (sMinus x y) := by
  have hB : M t (sPlus x y) ≠ 0 := by
    refine M_ne_zero t (ne_zero_of_im_ne_zero ?_) (ne_one_of_im_ne_zero ?_) <;>
      · rw [im_sPlus]; exact neg_ne_zero.mpr (by positivity)
  rw [B_apply]
  unfold f
  have hg : M t (sPlus x y) * gamma t x y = M t (sMinus x y) := by
    unfold gamma
    rw [show ((1 - y + x * I) / 2 : ℂ) = sMinus x y from rfl,
      show ((1 + y - x * I) / 2 : ℂ) = sPlus x y from rfl]
    exact mul_div_cancel₀ _ hB
  rw [mul_add, ← mul_assoc, hg, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    unfold mainTerm sStar
    ring
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    have hny : (n : ℂ) ^ (y : ℂ) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _
    unfold mainTerm
    rw [conj_sStar_add_kappa t x y hx, Complex.cpow_add _ _ hn0]
    field_simp

/-! ### Monotonicity in the tail constant -/

theorem epsTilde_nonneg {t : ℝ} {s : ℂ} (ht : 0 ≤ t) (hs : 100 ≤ s.im) : 0 ≤ epsTilde t s := by
  unfold epsTilde
  have hpi := Real.pi_lt_d2
  have hpi' := Real.pi_gt_d2
  have h1 : (0.865 : ℝ) < Real.sqrt ((s.im + π * t / 8) / (2 * π)) := by
    rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ (by positivity)]
    nlinarith
  have h2 : 0 ≤ 0.397 * (9 : ℝ) ^ s.re / (Real.sqrt ((s.im + π * t / 8) / (2 * π)) - 0.865) := by
    apply div_nonneg (by positivity); linarith
  have h3 : 0 ≤ 5 / (3 * (s.im - 6)) := by apply div_nonneg (by norm_num); linarith
  positivity

theorem TailEstimateWith.mono {K K' : ℝ} (hK : K ≤ K') (h : TailEstimateWith K) :
    TailEstimateWith K' := fun t x y hr => by
  refine (h t x y hr).trans (mul_le_mul_of_nonneg_right hK ?_)
  have h1 := epsTilde_nonneg (s := sMinus x y) hr.t_nonneg (by rw [im_sMinus]; linarith [hr.x_ge])
  have h2 := epsTilde_nonneg (s := (starRingEnd ℂ) (sPlus x y)) hr.t_nonneg
    (by rw [im_conj_sPlus]; linarith [hr.x_ge])
  positivity

end DeBruijnNewman
