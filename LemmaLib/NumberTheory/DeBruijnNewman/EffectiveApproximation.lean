/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.AlphaBounds
public import LemmaLib.NumberTheory.DeBruijnNewman.RiemannSiegel
public import LemmaLib.NumberTheory.DeBruijnNewman.RtnEstimate

/-!
# The effective approximation of `H t` from its Riemann–Siegel inputs

This file assembles Polymath Theorem 1.3 (*Effective approximation of heat flow evolution of the
Riemann ξ function*, Res. Math. Sci. 6 (2019)) from the two analytic inputs `RtnEstimate` and
`TailEstimate` of `LemmaLib.NumberTheory.DeBruijnNewman.RiemannSiegel`:

`effectiveApproximation_of : RtnEstimate → TailEstimate → EffectiveApproximation`.

Since `RtnEstimate` is proved in `LemmaLib.NumberTheory.DeBruijnNewman.RtnEstimate`, the theorem
reduces to `TailEstimate` alone (`effectiveApproximation_of_tail`).

The proof follows Section 6 of Polymath. The error `e_A + e_B` of the main terms is bounded
termwise by `errAB` (`termA_le`, `termB_le`, via the bound (6.12)–(6.13) on `ε_{t,n}` in
`epsR_le`), and the tail `exp(tπ²/64) |M₀(iT')| (1 + ε~(s₋) + ε~(conj s₊))` is bounded by
`|B_t| errC0` (`tail_le`, via `prefactor_log_le` and the numerical bound `epsTilde_sum_le` on
`ε~(s₋) + ε~(conj s₊)`).
-/

public section

open Complex Real Finset Set

namespace DeBruijnNewman

/-! ### The cutoff `N` -/

/-- `√((x/2 + πt/8)/(2π)) = √(x/(4π) + t/16)`, the quantity whose floor is `N`. -/
theorem sqrt_arg_eq (t x : ℝ) : (x / 2 + π * t / 8) / (2 * π) = x / (4 * π) + t / 16 := by
  field_simp
  ring

theorem cutoff_le_sqrt (t x : ℝ) :
    (cutoff t x : ℝ) ≤ Real.sqrt (x / (4 * π) + t / 16) :=
  Nat.floor_le (Real.sqrt_nonneg _)

theorem sqrt_lt_cutoff_add_one (t x : ℝ) :
    Real.sqrt (x / (4 * π) + t / 16) < (cutoff t x : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem three_le_cutoff {t x : ℝ} (ht : 0 ≤ t) (hx : 200 ≤ x) : 3 ≤ cutoff t x := by
  unfold cutoff
  apply Nat.le_floor
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  have hpi := Real.pi_lt_d2
  have h1 : 9 ≤ x / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h2 : 0 ≤ t / 16 := by positivity
  push_cast
  linarith

/-- For `1 ≤ n ≤ N`, `n² ≤ x/(4π) + 1/32`. -/
theorem sq_le_of_le_cutoff {t x : ℝ} {n : ℕ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hx : 200 ≤ x)
    (hn : n ≤ cutoff t x) : (n : ℝ) ^ 2 ≤ x / (4 * π) + 1 / 32 := by
  have h1 : (n : ℝ) ≤ Real.sqrt (x / (4 * π) + t / 16) :=
    (Nat.cast_le.mpr hn).trans (cutoff_le_sqrt t x)
  have h2 : (n : ℝ) ^ 2 ≤ x / (4 * π) + t / 16 := by
    calc (n : ℝ) ^ 2 ≤ Real.sqrt (x / (4 * π) + t / 16) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = x / (4 * π) + t / 16 := Real.sq_sqrt (by positivity)
  linarith

/-- `x ≥ 4πN² - 0.4`. -/
theorem four_pi_cutoff_sq_le {t x : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hx : 200 ≤ x) :
    4 * π * (cutoff t x : ℝ) ^ 2 ≤ x + 0.4 := by
  have hpi := Real.pi_lt_d2
  have h1 : (cutoff t x : ℝ) ^ 2 ≤ x / (4 * π) + t / 16 := by
    have h := cutoff_le_sqrt t x
    calc (cutoff t x : ℝ) ^ 2 ≤ Real.sqrt (x / (4 * π) + t / 16) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h 2
      _ = x / (4 * π) + t / 16 := Real.sq_sqrt (by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * π)
  have e : 4 * π * (x / (4 * π) + t / 16) = x + π * t / 4 := by field_simp; ring
  rw [e] at h2
  have : π * t ≤ 3.15 * (1 / 2) := mul_le_mul hpi.le ht ht0 (by norm_num)
  linarith

/-! ### The error `ε_{t,n}` on the horizontal line `Im s = x/2` -/

/-- `ε_{t,n}(σ + ix/2) ≤ exp ((t²/16 log² (x/(4πn²)) + 0.626) / (x - 6.66)) - 1` (Polymath
(6.12)–(6.13)). -/
theorem epsR_le {t x σ : ℝ} {n : ℕ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hx : 200 ≤ x) (hn : 1 ≤ n) (hnx : (n : ℝ) ^ 2 ≤ x / (4 * π) + 1 / 32) :
    epsR t n (σ + (x / 2 : ℝ) * I) ≤
      Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66)) -
        1 := by
  unfold epsR
  have him : ((σ : ℂ) + (x / 2 : ℝ) * I).im = x / 2 := by simp
  rw [him]
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have hA := norm_alpha_sub_log_sq_le hσ0 hσ1 hx hn hnx
  set A := ‖alpha (σ + (x / 2 : ℝ) * I) - Real.log n‖ ^ 2 with hAdef
  set L2 := Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 with hL2
  have hL2n : 0 ≤ L2 := sq_nonneg _
  have hx6 : 0 < x - 6.66 := by norm_num; linarith
  rw [show x / 2 - 3.33 = (x - 6.66) / 2 by ring, div_div_eq_mul_div,
    div_le_div_iff_of_pos_right hx6]
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  have h1 : t ^ 2 / 8 * A ≤ t ^ 2 / 8 * (1 / 4 * L2 + 667 / 1000) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have h2 : t ^ 2 / 8 * (667 / 1000) ≤ 1 / 4 * (667 / 1000) / 8 := by nlinarith
  nlinarith


/-! ### The sum `ε~(s₋) + ε~(conj s₊)` -/

theorem cutoff_poly_ineq {N : ℝ} (hN : 3 ≤ N) :
    0.9605 / (N - 0.865) * ((12.56 * N ^ 2 - 1.14) / (12.56 * N ^ 2 - 8.4)) ≤
      (N + 1.115) / (N - 0.125) ^ 2 := by
  have hm : 0 ≤ N - 3 := by linarith
  have h1 : 0 < N - 0.865 := by norm_num; linarith
  have h2 : 0 < 12.56 * N ^ 2 - 8.4 := by nlinarith
  have h3 : 0 < (N - 0.125) ^ 2 := by
    have : 0 < N - 0.125 := by norm_num; linarith
    positivity
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) h3]
  nlinarith [pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, mul_nonneg hm (pow_nonneg hm 2)]

theorem exp_le_of_le_small {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 0.04) : Real.exp u ≤ 1 + 1.04 * u := by
  have := Real.exp_bound' hu0 (by linarith) (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at this
  nlinarith

theorem two_le_rpow_add_rpow_neg (y : ℝ) : 2 ≤ (3 : ℝ) ^ y + (3 : ℝ) ^ (-y) := by
  have hu : 0 < (3 : ℝ) ^ y := by positivity
  rw [Real.rpow_neg (by norm_num)]
  have : (3 : ℝ) ^ y + ((3 : ℝ) ^ y)⁻¹ - 2 = ((3 : ℝ) ^ y - 1) ^ 2 / (3 : ℝ) ^ y := by
    field_simp; ring
  have : 0 ≤ (3 : ℝ) ^ y + ((3 : ℝ) ^ y)⁻¹ - 2 := by rw [this]; positivity
  linarith

theorem nine_rpow (u : ℝ) : (9 : ℝ) ^ (u / 2) = (3 : ℝ) ^ u := by
  rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

theorem epsTilde_sMinus (t x y : ℝ) :
    epsTilde t (sMinus x y) =
      (0.397 * (3 * (3 : ℝ) ^ (-y)) / (Real.sqrt (x / (4 * π) + t / 16) - 0.865) +
        5 / (3 * (x / 2 - 6))) * Real.exp (3.49 / (x / 2 - 4)) := by
  unfold epsTilde
  rw [re_sMinus, im_sMinus, sqrt_arg_eq, nine_rpow, Real.rpow_sub (by norm_num), Real.rpow_one,
    Real.rpow_neg (by norm_num)]
  ring

theorem epsTilde_conj_sPlus (t x y : ℝ) :
    epsTilde t ((starRingEnd ℂ) (sPlus x y)) =
      (0.397 * (3 * (3 : ℝ) ^ y) / (Real.sqrt (x / (4 * π) + t / 16) - 0.865) +
        5 / (3 * (x / 2 - 6))) * Real.exp (3.49 / (x / 2 - 4)) := by
  unfold epsTilde
  rw [re_conj_sPlus, im_conj_sPlus, sqrt_arg_eq, nine_rpow, Real.rpow_add (by norm_num),
    Real.rpow_one]

/-- `1 + 1.04 u ≤ (12.56 N² - 1.14)/(12.56 N² - 8.4)` for `u = 3.49/(x/2 - 4)` and
`x ≥ 4πN² - 0.4`. -/
theorem one_add_u_le {N x : ℝ} (hN : 3 ≤ N) (hx : 200 ≤ x) (hxN : 4 * π * N ^ 2 ≤ x + 0.4) :
    1 + 1.04 * (3.49 / (x / 2 - 4)) ≤ (12.56 * N ^ 2 - 1.14) / (12.56 * N ^ 2 - 8.4) := by
  have hpi := Real.pi_gt_d2
  have hD : 0 < 12.56 * N ^ 2 - 8.4 := by nlinarith
  have h1 : 12.56 * N ^ 2 - 8.4 ≤ x - 8 := by nlinarith [sq_nonneg N]
  have h2 : 1.04 * (3.49 / (x / 2 - 4)) ≤ 7.26 / (12.56 * N ^ 2 - 8.4) := by
    rw [show (1.04 : ℝ) * (3.49 / (x / 2 - 4)) = 7.2592 / (x - 8) by
      rw [mul_div_assoc', div_eq_div_iff (by linarith) (by linarith)]; ring]
    calc (7.2592 : ℝ) / (x - 8) ≤ 7.2592 / (12.56 * N ^ 2 - 8.4) :=
          div_le_div_of_nonneg_left (by norm_num) hD h1
      _ ≤ 7.26 / (12.56 * N ^ 2 - 8.4) := by gcongr; norm_num
  rw [show (12.56 * N ^ 2 - 1.14) / (12.56 * N ^ 2 - 8.4) = 1 + 7.26 / (12.56 * N ^ 2 - 8.4) by
    field_simp; ring]
  linarith

/-- The `N`-dependent part of (6.19). -/
theorem S_part_le {N c' v : ℝ} (hN : 3 ≤ N) (hc' : 2 ≤ c') (hv0 : 0 ≤ v)
    (hv : v ≤ (12.56 * N ^ 2 - 1.14) / (12.56 * N ^ 2 - 8.4)) :
    1.191 * c' / (N - 0.865) * v ≤
      1.24 * c' / (N - 0.125) + (1.24 * c') ^ 2 / (2 * (N - 0.125) ^ 2) := by
  have hN0 : 0 < N - 0.865 := by norm_num; linarith
  have hN1 : 0 < N - 0.125 := by norm_num; linarith
  have hD : 0 < 12.56 * N ^ 2 - 8.4 := by nlinarith
  have hpos : 0 ≤ (12.56 * N ^ 2 - 1.14) / (12.56 * N ^ 2 - 8.4) := by
    apply div_nonneg _ hD.le; nlinarith
  have step1 : 1.191 * c' / (N - 0.865) * v ≤
      1.24 * c' * (0.9605 / (N - 0.865)) * ((12.56 * N ^ 2 - 1.14) / (12.56 * N ^ 2 - 8.4)) := by
    have : 1.191 * c' / (N - 0.865) ≤ 1.24 * c' * (0.9605 / (N - 0.865)) := by
      rw [show (1.24 : ℝ) * c' * (0.9605 / (N - 0.865)) = 1.19102 * c' / (N - 0.865) by ring]
      apply div_le_div_of_nonneg_right _ hN0.le
      nlinarith
    exact mul_le_mul this hv hv0 (by positivity)
  have step2 : 1.24 * c' * (0.9605 / (N - 0.865)) *
      ((12.56 * N ^ 2 - 1.14) / (12.56 * N ^ 2 - 8.4)) ≤
        1.24 * c' * ((N + 1.115) / (N - 0.125) ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (cutoff_poly_ineq hN) (by linarith)
  have step3 : 1.24 * c' * ((N + 1.115) / (N - 0.125) ^ 2) ≤
      1.24 * c' / (N - 0.125) + (1.24 * c') ^ 2 / (2 * (N - 0.125) ^ 2) := by
    have e1 : 1.24 * c' * ((N + 1.115) / (N - 0.125) ^ 2) =
        1.24 * c' / (N - 0.125) + 1.24 * 1.24 * c' / (N - 0.125) ^ 2 := by
      field_simp; ring
    have e2 : 1.24 * 1.24 * c' / (N - 0.125) ^ 2 ≤ (1.24 * c') ^ 2 / (2 * (N - 0.125) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c') (by linarith : 0 ≤ c' - 2))
        (sq_nonneg (N - 0.125))]
    linarith
  linarith

/-- The numerical core of Polymath (6.17)–(6.19), with `p = 3^y`, `q = 3^{-y}`,
`N ≤ a = √(x/4π + t/16)` and `x ≥ 4πN² - 0.4`. -/
theorem epsTilde_core {N a x p q : ℝ} (hN : 3 ≤ N) (hNa : N ≤ a) (hx : 200 ≤ x)
    (hxN : 4 * π * N ^ 2 ≤ x + 0.4) (hpq : 2 ≤ p + q) :
    (0.397 * (3 * q) / (a - 0.865) + 5 / (3 * (x / 2 - 6))) * Real.exp (3.49 / (x / 2 - 4)) +
      (0.397 * (3 * p) / (a - 0.865) + 5 / (3 * (x / 2 - 6))) * Real.exp (3.49 / (x / 2 - 4)) ≤
      (1.24 * (p + q) / (N - 0.125) + 7 / (x - 12)) +
        (1.24 * (p + q) / (N - 0.125) + 7 / (x - 12)) ^ 2 / 2 := by
  have hx12 : 0 < x - 12 := by linarith
  have hN0 : 0 < N - 0.865 := by norm_num; linarith
  have hN1 : 0 < N - 0.125 := by norm_num; linarith
  have ha0 : 0 < a - 0.865 := by norm_num; linarith
  have huN := one_add_u_le hN hx hxN
  set c' := p + q with hc'
  set u := 3.49 / (x / 2 - 4) with hu
  have hu0 : 0 ≤ u := by rw [hu]; apply div_nonneg (by norm_num); linarith
  have hu1 : u ≤ 0.04 := by
    rw [hu, div_le_iff₀ (by linarith)]; linarith
  have hexp := exp_le_of_le_small hu0 hu1
  have hux : 1.04 * u ≤ 0.0379 := by
    have : u ≤ 3.49 / 96 := by
      rw [hu]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
    norm_num at this ⊢; linarith
  -- rewrite the left-hand side
  have eL : (0.397 * (3 * q) / (a - 0.865) + 5 / (3 * (x / 2 - 6))) * Real.exp u +
      (0.397 * (3 * p) / (a - 0.865) + 5 / (3 * (x / 2 - 6))) * Real.exp u =
      (1.191 * c' / (a - 0.865) + 20 / (3 * (x - 12))) * Real.exp u := by
    rw [hc']
    have e : 5 / (3 * (x / 2 - 6)) = 10 / (3 * (x - 12)) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [e]; ring
  rw [eL]
  set S := 1.191 * c' / (a - 0.865) with hS
  set R := 20 / (3 * (x - 12)) with hR
  have hS0 : 0 ≤ S := by rw [hS]; apply div_nonneg (by linarith) ha0.le
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have step1 : (S + R) * Real.exp u ≤ (S + R) * (1 + 1.04 * u) :=
    mul_le_mul_of_nonneg_left hexp (by linarith)
  -- the `S` part
  have hS1 : S ≤ 1.191 * c' / (N - 0.865) := by
    rw [hS]; apply div_le_div_of_nonneg_left (by linarith) hN0; linarith
  have hS2 : S * (1 + 1.04 * u) ≤
      1.24 * c' / (N - 0.125) + (1.24 * c') ^ 2 / (2 * (N - 0.125) ^ 2) :=
    (mul_le_mul_of_nonneg_right hS1 (by linarith)).trans
      (S_part_le hN (by rw [hc']; exact hpq) (by linarith) huN)
  -- the `R` part
  have hR2 : R * (1 + 1.04 * u) ≤ 6.92 / (x - 12) := by
    calc R * (1 + 1.04 * u) ≤ R * 1.0379 := mul_le_mul_of_nonneg_left (by linarith) hR0
      _ = 20 * 1.0379 / 3 / (x - 12) := by rw [hR]; field_simp
      _ ≤ 6.92 / (x - 12) := by gcongr; norm_num
  -- assemble
  set w := 1.24 * c' / (N - 0.125) + 7 / (x - 12) with hw
  have hw1 : 1.24 * c' / (N - 0.125) ≤ w := by
    rw [hw]; have : 0 ≤ 7 / (x - 12) := by positivity
    linarith
  have hw0 : 0 ≤ 1.24 * c' / (N - 0.125) := by positivity
  have hw2 : (1.24 * c') ^ 2 / (2 * (N - 0.125) ^ 2) ≤ w ^ 2 / 2 := by
    rw [show (1.24 * c') ^ 2 / (2 * (N - 0.125) ^ 2) = (1.24 * c' / (N - 0.125)) ^ 2 / 2 by
      field_simp]
    gcongr
  have h7 : 6.92 / (x - 12) ≤ 7 / (x - 12) := by gcongr; norm_num
  nlinarith [step1, hS2, hR2, hw2, h7]

/-- Polymath (6.17)–(6.19): the sum `ε~(s₋) + ε~(conj s₊)` is at most `w + w²/2` where
`w = 1.24 (3^y + 3^{-y}) / (N - 0.125) + 7/(x - 12)`. -/
theorem epsTilde_sum_le {t x y : ℝ} (hr : InRegion t x y) :
    epsTilde t (sMinus x y) + epsTilde t ((starRingEnd ℂ) (sPlus x y)) ≤
      (1.24 * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) / ((cutoff t x : ℝ) - 0.125) + 7 / (x - 12)) +
        (1.24 * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) / ((cutoff t x : ℝ) - 0.125) + 7 / (x - 12)) ^ 2
          / 2 := by
  obtain ⟨ht0, ht, _, _, hx⟩ := hr
  rw [epsTilde_sMinus, epsTilde_conj_sPlus]
  exact epsTilde_core (by exact_mod_cast three_le_cutoff ht0 hx) (cutoff_le_sqrt t x) hx
    (four_pi_cutoff_sq_le ht0 ht hx) (two_le_rpow_add_rpow_neg y)


/-! ### The bound `e_{C,0} ≤ |B_t| · errC0` -/

/-- Polymath (6.15)–(6.19): the tail `exp(tπ²/64) |M₀(iT')| (1 + ε~(s₋) + ε~(conj s₊))` is at most
`|M_t(s₊)| · errC0`. -/
theorem tail_le {t x y : ℝ} (hr : InRegion t x y) :
    Real.exp (t * π ^ 2 / 64) * ‖M₀ (((x / 2 + π * t / 8 : ℝ) : ℂ) * I)‖ *
      (1 + epsTilde t (sMinus x y) + epsTilde t ((starRingEnd ℂ) (sPlus x y))) ≤
      ‖M t (sPlus x y)‖ * errC0 t x y := by
  have hq := epsTilde_sum_le hr
  obtain ⟨ht0, ht, hy0, hy1, hx⟩ := hr
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  have hx0 : 0 < x := by linarith
  have hx12 : 0 < x - 12 := by linarith
  have hpre := prefactor_log_le ht0 ht hy0 hy1 hx
  have hzim : ((((x / 2 + π * t / 8 : ℝ) : ℂ) * I)).im ≠ 0 := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one]
    positivity
  have hsim : (sPlus x y).im ≠ 0 := by
    rw [im_sPlus]; exact neg_ne_zero.mpr (by positivity)
  rw [norm_M₀ (ne_zero_of_im_ne_zero hzim) (ne_one_of_im_ne_zero hzim),
    norm_M (ne_zero_of_im_ne_zero hsim) (ne_one_of_im_ne_zero hsim)]
  unfold errC0
  rw [Real.rpow_def_of_pos (by positivity)]
  set L := Real.log (x / (4 * π)) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]; apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hLle : L ≤ x / 34 := log_div_four_pi_le hx
  set N := (cutoff t x : ℝ) with hN
  set c' := (3 : ℝ) ^ y + (3 : ℝ) ^ (-y) with hc'
  set w := 1.24 * c' / (N - 0.125) + 7 / (x - 12) with hw
  have hN3 : (3 : ℝ) ≤ N := by rw [hN]; exact_mod_cast three_le_cutoff ht0 hx
  have hw0 : 0 ≤ w := by
    rw [hw]
    have : 0 < N - 0.125 := by norm_num; linarith
    have : 0 ≤ c' := by positivity
    positivity
  have hqexp : 1 + epsTilde t (sMinus x y) + epsTilde t ((starRingEnd ℂ) (sPlus x y)) ≤
      Real.exp w := by
    have h1 : 1 + epsTilde t (sMinus x y) + epsTilde t ((starRingEnd ℂ) (sPlus x y)) ≤
        1 + w + w ^ 2 / 2 := by linarith [hq]
    exact h1.trans (Real.quadratic_le_exp_of_nonneg hw0)
  -- the exponent gap
  set A := (logM₀ (((x / 2 + π * t / 8 : ℝ) : ℂ) * I)).re with hA
  set S := (logM t (sPlus x y)).re with hS
  set E := -(t / 16) * L ^ 2 + 1.24 * c' / (N - 0.125) +
    (3 * Real.sqrt (L ^ 2 + (π / 2) ^ 2) + 10.44) / (x - 12) with hE
  have hsq : π / 2 ≤ Real.sqrt (L ^ 2 + (π / 2) ^ 2) := by
    have := Real.sqrt_le_sqrt (show (π / 2) ^ 2 ≤ L ^ 2 + (π / 2) ^ 2 by nlinarith [sq_nonneg L])
    rwa [Real.sqrt_sq (by positivity)] at this
  have hnum1 : 15.15 / (x - 12) ≤ (3 * Real.sqrt (L ^ 2 + (π / 2) ^ 2) + 10.44) / (x - 12) := by
    apply div_le_div_of_nonneg_right _ hx12.le; linarith
  have hnum2 : 3.58 / (x - 6) ≤ 3.58 / (x - 12) :=
    div_le_div_of_nonneg_left (by norm_num) hx12 (by linarith)
  have hnum3 : L / (2 * x ^ 2) ≤ 0.02 / (x - 12) := by
    calc L / (2 * x ^ 2) ≤ x / 34 / (2 * x ^ 2) := by gcongr
      _ = 1 / (68 * x) := by field_simp; ring
      _ ≤ 0.02 / (x - 12) := by
          rw [div_le_div_iff₀ (by positivity) hx12]; linarith
  have hgap : w ≤ S + L * (-(1 + y) / 4) + E - (t * π ^ 2 / 64 + A) := by
    have hinv : 0 < (x - 12)⁻¹ := inv_pos.mpr hx12
    rw [hw, hE]
    simp only [div_eq_mul_inv] at hpre hnum1 hnum2 hnum3 ⊢
    linarith
  calc Real.exp (t * π ^ 2 / 64) * Real.exp A *
        (1 + epsTilde t (sMinus x y) + epsTilde t ((starRingEnd ℂ) (sPlus x y)))
      ≤ Real.exp (t * π ^ 2 / 64) * Real.exp A * Real.exp w := by gcongr
    _ ≤ Real.exp (t * π ^ 2 / 64) * Real.exp A *
        Real.exp (S + L * (-(1 + y) / 4) + E - (t * π ^ 2 / 64 + A)) := by gcongr
    _ = Real.exp S * (Real.exp (L * (-(1 + y) / 4)) * Real.exp E) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1; ring


/-! ### The main terms at `s₋` and `conj s₊` -/

theorem M_sMinus_eq (t x y : ℝ) (hx : x ≠ 0) :
    M t (sMinus x y) = M t (sPlus x y) * gamma t x y := by
  have hB : M t (sPlus x y) ≠ 0 := by
    refine M_ne_zero t (ne_zero_of_im_ne_zero ?_) (ne_one_of_im_ne_zero ?_) <;>
      · rw [im_sPlus]; exact neg_ne_zero.mpr (by positivity)
  unfold gamma
  rw [show ((1 - y + x * I) / 2 : ℂ) = sMinus x y from rfl,
    show ((1 + y - x * I) / 2 : ℂ) = sPlus x y from rfl]
  exact (mul_div_cancel₀ _ hB).symm

theorem norm_mainTerm_sPlus (t x y : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖mainTerm t n (sPlus x y)‖ = ‖M t (sPlus x y)‖ * b t n / (n : ℝ) ^ (sStar t x y).re :=
  norm_mainTerm t hn _

theorem norm_mainTerm_sMinus (t x y : ℝ) {n : ℕ} (hn : 0 < n) (hx : x ≠ 0) :
    ‖mainTerm t n (sMinus x y)‖ = ‖gamma t x y‖ * ‖M t (sPlus x y)‖ * b t n /
      (n : ℝ) ^ ((sStar t x y).re + (kappa t x y).re - y) := by
  rw [norm_mainTerm t hn, M_sMinus_eq t x y hx, norm_mul]
  have e : (sMinus x y + t / 2 * alpha (sMinus x y)).re =
      (sStar t x y).re + (kappa t x y).re - y := by
    have := conj_sStar_add_kappa t x y hx
    have e2 : sMinus x y + t / 2 * alpha (sMinus x y) =
        (starRingEnd ℂ) (sStar t x y) + kappa t x y - y := by rw [this]; ring
    rw [e2, Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.ofReal_re]
  rw [e]
  ring

/-- `mainTerm t n s₊ = conj (mainTerm t n (conj s₊))`. -/
theorem mainTerm_sPlus_eq_conj (t x y : ℝ) (n : ℕ) (hx : 0 < x) :
    mainTerm t n (sPlus x y) = (starRingEnd ℂ) (mainTerm t n ((starRingEnd ℂ) (sPlus x y))) := by
  have him : ((starRingEnd ℂ) (sPlus x y)).im ≠ 0 := by
    rw [im_conj_sPlus]; positivity
  rw [← mainTerm_conj t n him, Complex.conj_conj]

/-- `ε_{t,n}(s) ≥ 0` when `Im s > 3.33`. -/
theorem epsR_nonneg {t : ℝ} (ht0 : 0 ≤ t) (n : ℕ) {s : ℂ} (hs : 3.33 < s.im) :
    0 ≤ epsR t n s := by
  unfold epsR
  rw [sub_nonneg, Real.one_le_exp_iff]
  apply div_nonneg _ (by linarith)
  positivity

/-- The `n`-th term of `e_B`, Polymath (6.12). -/
theorem termB_le (hR : RtnEstimate) {t x y : ℝ} (hr : InRegion t x y) {n : ℕ}
    (hn : n ∈ Finset.Icc 1 (cutoff t x)) :
    ‖(starRingEnd ℂ) (r t n ((starRingEnd ℂ) (sPlus x y))) - mainTerm t n (sPlus x y)‖ ≤
      ‖M t (sPlus x y)‖ * (b t n / (n : ℝ) ^ (sStar t x y).re *
        (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66))
          - 1)) := by
  obtain ⟨ht0, ht, hy0, hy1, hx⟩ := hr
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hx0 : 0 < x := by linarith
  have hn0 : 0 < n := hn1
  have him : ((starRingEnd ℂ) (sPlus x y)).im = x / 2 := im_conj_sPlus x y
  have hest := hR t n _ ht0 ht hn1 (by rw [him]; linarith)
  rw [mainTerm_sPlus_eq_conj t x y n hx0, ← map_sub, Complex.norm_conj]
  refine hest.trans ?_
  have hnorm : ‖mainTerm t n ((starRingEnd ℂ) (sPlus x y))‖ =
      ‖M t (sPlus x y)‖ * b t n / (n : ℝ) ^ (sStar t x y).re := by
    rw [← Complex.norm_conj, ← mainTerm_sPlus_eq_conj t x y n hx0]
    exact norm_mainTerm_sPlus t x y hn0
  rw [hnorm]
  have heps : epsR t n ((starRingEnd ℂ) (sPlus x y)) ≤
      Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66)) -
        1 := by
    rw [conj_sPlus]
    exact epsR_le ht0 ht (by linarith) (by linarith) hx hn1 (sq_le_of_le_cutoff ht0 ht hx hnN)
  have h0 : 0 ≤ epsR t n ((starRingEnd ℂ) (sPlus x y)) := epsR_nonneg ht0 n (by rw [him]; linarith)
  calc ‖M t (sPlus x y)‖ * b t n / (n : ℝ) ^ (sStar t x y).re *
        epsR t n ((starRingEnd ℂ) (sPlus x y))
      ≤ ‖M t (sPlus x y)‖ * b t n / (n : ℝ) ^ (sStar t x y).re *
        (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66))
          - 1) := by
        apply mul_le_mul_of_nonneg_left heps
        have := b_pos t n
        positivity
    _ = _ := by ring

/-- The `n`-th term of `e_A`, Polymath (6.11). -/
theorem termA_le (hR : RtnEstimate) {t x y : ℝ} (hr : InRegion t x y) {n : ℕ}
    (hn : n ∈ Finset.Icc 1 (cutoff t x)) :
    ‖r t n (sMinus x y) - mainTerm t n (sMinus x y)‖ ≤
      ‖M t (sPlus x y)‖ * (‖gamma t x y‖ * (cutoff t x : ℝ) ^ ‖kappa t x y‖ * (n : ℝ) ^ y *
        b t n / (n : ℝ) ^ (sStar t x y).re *
        (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66))
          - 1)) := by
  obtain ⟨ht0, ht, hy0, hy1, hx⟩ := hr
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hx0 : 0 < x := by linarith
  have hn0 : 0 < n := hn1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have him : (sMinus x y).im = x / 2 := im_sMinus x y
  have hest := hR t n _ ht0 ht hn1 (by rw [him]; linarith)
  refine hest.trans ?_
  rw [norm_mainTerm_sMinus t x y hn0 hx0.ne']
  have heps : epsR t n (sMinus x y) ≤
      Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66)) -
        1 := by
    rw [sMinus_eq']
    exact epsR_le ht0 ht (by linarith) (by linarith) hx hn1 (sq_le_of_le_cutoff ht0 ht hx hnN)
  have h0 : 0 ≤ epsR t n (sMinus x y) := epsR_nonneg ht0 n (by rw [him]; linarith)
  -- `n^{-(Re s* + Re κ - y)} = n^y n^{-Re s*} n^{-Re κ}` and `n^{-Re κ} ≤ N^{|κ|}`
  have hκ : (n : ℝ) ^ (-(kappa t x y).re) ≤ (cutoff t x : ℝ) ^ ‖kappa t x y‖ := by
    calc (n : ℝ) ^ (-(kappa t x y).re) ≤ (n : ℝ) ^ ‖kappa t x y‖ := by
          apply Real.rpow_le_rpow_of_exponent_le hnr1
          have := Complex.abs_re_le_norm (kappa t x y)
          linarith [neg_abs_le (kappa t x y).re]
      _ ≤ (cutoff t x : ℝ) ^ ‖kappa t x y‖ :=
          Real.rpow_le_rpow hnr.le (by exact_mod_cast hnN) (norm_nonneg _)
  have e : ‖gamma t x y‖ * ‖M t (sPlus x y)‖ * b t n /
      (n : ℝ) ^ ((sStar t x y).re + (kappa t x y).re - y) =
      ‖M t (sPlus x y)‖ * (‖gamma t x y‖ * (n : ℝ) ^ (-(kappa t x y).re) * (n : ℝ) ^ y *
        b t n / (n : ℝ) ^ (sStar t x y).re) := by
    rw [Real.rpow_sub hnr, Real.rpow_add hnr, Real.rpow_neg hnr.le]
    have h1 : (n : ℝ) ^ (sStar t x y).re ≠ 0 := (Real.rpow_pos_of_pos hnr _).ne'
    have h2 : (n : ℝ) ^ (kappa t x y).re ≠ 0 := (Real.rpow_pos_of_pos hnr _).ne'
    have h3 : (n : ℝ) ^ y ≠ 0 := (Real.rpow_pos_of_pos hnr _).ne'
    field_simp
  rw [e]
  have hb := b_pos t n
  have hM := norm_nonneg (M t (sPlus x y))
  have hγ := norm_nonneg (gamma t x y)
  have hny : 0 ≤ (n : ℝ) ^ y := Real.rpow_nonneg hnr.le _
  have hns : 0 < (n : ℝ) ^ (sStar t x y).re := Real.rpow_pos_of_pos hnr _
  have hmain : ‖gamma t x y‖ * (n : ℝ) ^ (-(kappa t x y).re) * (n : ℝ) ^ y * b t n /
      (n : ℝ) ^ (sStar t x y).re ≤
      ‖gamma t x y‖ * (cutoff t x : ℝ) ^ ‖kappa t x y‖ * (n : ℝ) ^ y * b t n /
        (n : ℝ) ^ (sStar t x y).re := by
    gcongr
  calc ‖M t (sPlus x y)‖ * (‖gamma t x y‖ * (n : ℝ) ^ (-(kappa t x y).re) * (n : ℝ) ^ y *
        b t n / (n : ℝ) ^ (sStar t x y).re) * epsR t n (sMinus x y)
      ≤ ‖M t (sPlus x y)‖ * (‖gamma t x y‖ * (cutoff t x : ℝ) ^ ‖kappa t x y‖ * (n : ℝ) ^ y *
        b t n / (n : ℝ) ^ (sStar t x y).re) *
        (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66))
          - 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hmain hM) heps h0
        have : 0 ≤ (cutoff t x : ℝ) ^ ‖kappa t x y‖ := Real.rpow_nonneg (by positivity) _
        positivity
    _ = _ := by ring

/-! ### The effective approximation -/

/-- Polymath Theorem 1.3 (in the form `EffectiveApproximation`), assuming the Riemann–Siegel
inputs `RtnEstimate` (Proposition 6.1) and `TailEstimate` (the expansion (5.4) with the
remainder bound of Proposition 6.3). -/
theorem effectiveApproximation_of (hR : RtnEstimate) (hT : TailEstimate) :
    EffectiveApproximation := by
  intro t x y hr
  have hx0 : 0 < x := by linarith [hr.x_ge]
  rw [B_mul_f t x y hx0.ne', B_apply]
  have htail := (hT t x y hr).trans (tail_le hr)
  have hA := fun n (hn : n ∈ Finset.Icc 1 (cutoff t x)) => termA_le hR hr hn
  have hB := fun n (hn : n ∈ Finset.Icc 1 (cutoff t x)) => termB_le hR hr hn
  unfold errAB
  set N := cutoff t x
  set Mp := ‖M t (sPlus x y)‖
  have e : H t (x + y * I) - (∑ n ∈ Icc 1 N, mainTerm t n (sPlus x y) +
      ∑ n ∈ Icc 1 N, mainTerm t n (sMinus x y)) =
      (H t (x + y * I) - ∑ n ∈ Icc 1 N, r t n (sMinus x y) -
        ∑ n ∈ Icc 1 N, (starRingEnd ℂ) (r t n ((starRingEnd ℂ) (sPlus x y)))) +
      ∑ n ∈ Icc 1 N, (r t n (sMinus x y) - mainTerm t n (sMinus x y)) +
      ∑ n ∈ Icc 1 N, ((starRingEnd ℂ) (r t n ((starRingEnd ℂ) (sPlus x y))) -
        mainTerm t n (sPlus x y)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; ring
  rw [e]
  calc ‖_ + _ + _‖ ≤ ‖H t (x + y * I) - ∑ n ∈ Icc 1 N, r t n (sMinus x y) -
        ∑ n ∈ Icc 1 N, (starRingEnd ℂ) (r t n ((starRingEnd ℂ) (sPlus x y)))‖ +
        ‖∑ n ∈ Icc 1 N, (r t n (sMinus x y) - mainTerm t n (sMinus x y))‖ +
        ‖∑ n ∈ Icc 1 N, ((starRingEnd ℂ) (r t n ((starRingEnd ℂ) (sPlus x y))) -
          mainTerm t n (sPlus x y))‖ := norm_add₃_le
    _ ≤ Mp * errC0 t x y +
        ∑ n ∈ Icc 1 N, ‖r t n (sMinus x y) - mainTerm t n (sMinus x y)‖ +
        ∑ n ∈ Icc 1 N, ‖(starRingEnd ℂ) (r t n ((starRingEnd ℂ) (sPlus x y))) -
          mainTerm t n (sPlus x y)‖ := by
        exact add_le_add (add_le_add htail (norm_sum_le _ _)) (norm_sum_le _ _)
    _ ≤ Mp * errC0 t x y +
        ∑ n ∈ Icc 1 N, Mp * (‖gamma t x y‖ * (N : ℝ) ^ ‖kappa t x y‖ * (n : ℝ) ^ y *
          b t n / (n : ℝ) ^ (sStar t x y).re *
          (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66))
            - 1)) +
        ∑ n ∈ Icc 1 N, Mp * (b t n / (n : ℝ) ^ (sStar t x y).re *
          (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) / (x - 6.66))
            - 1)) := by
        exact add_le_add (add_le_add le_rfl (Finset.sum_le_sum hA)) (Finset.sum_le_sum hB)
    _ = _ := by
        have hsum : ∑ n ∈ Finset.Icc 1 N, (‖gamma t x y‖ * (N : ℝ) ^ ‖kappa t x y‖ * (n : ℝ) ^ y *
              b t n / (n : ℝ) ^ (sStar t x y).re *
              (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) /
                (x - 6.66)) - 1) +
            b t n / (n : ℝ) ^ (sStar t x y).re *
              (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) /
                (x - 6.66)) - 1)) =
            ∑ n ∈ Finset.Icc 1 N, (1 + ‖gamma t x y‖ * (N : ℝ) ^ ‖kappa t x y‖ * (n : ℝ) ^ y) *
              b t n / (n : ℝ) ^ (sStar t x y).re *
              (Real.exp ((t ^ 2 / 16 * Real.log (x / (4 * π * (n : ℝ) ^ 2)) ^ 2 + 0.626) /
                (x - 6.66)) - 1) := by
          apply Finset.sum_congr rfl
          intro n _
          ring
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← hsum, Finset.sum_add_distrib]
        ring

/-- Polymath Theorem 1.3, assuming only the Riemann–Siegel expansion `TailEstimate`. -/
theorem effectiveApproximation_of_tail (hT : TailEstimate) : EffectiveApproximation :=
  effectiveApproximation_of rtnEstimate hT

end DeBruijnNewman
