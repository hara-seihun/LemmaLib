/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.RiemannSiegel.Fold
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Riemann–Siegel formula

For `s` not an integer,
`(1/8) ξ(s) = R_{0,0}(s) + conj (R_{0,0}(1 - conj s))`
(`RiemannSiegel.formula`; Titchmarsh (2.10.6), Polymath (5.3)), where `ξ(s)/8 = s(s-1)/16 · Λ(s)`
with `Λ` the completed zeta function and
`R_{0,N}(s) = s(s-1)/16 · Γ_ℝ(s) · ∫_{N+1/2 ↙} w^{-s} e^{iπw²} / (e^{iπw} - e^{-iπw}) dw`
(`RiemannSiegel.remainder N s`).

For `Re s > 2` the formula is the sum of the Mellin form `R(s) = ζ(s) - ω^s (2π)^s / Γ(s) · I₀(s)`
(`rsIntegral_eq_zeta_sub`) and the fold `conj (R(1 - conj s)) = e^{-iπs/4} (1 + e^{iπs}) I₀(s)`
(`conj_rsIntegral_one_sub`), with the reflection formula for `Γ_ℝ` matching the two coefficients
of `I₀(s)`. Both sides are analytic off the integers, so the identity theorem extends it.

The residue expansion `R_{0,0}(s) = ∑_{n=1}^N r_{0,n}(s) + R_{0,N}(s)` (`remainder_zero_eq`) then
gives the expansion of `ξ(s)/8` in `N` main terms and a remainder (`formula_expand`).
-/

public section

open Complex Real Set Filter Topology MeasureTheory

local notation "ω" => Complex.rsOmega

namespace RiemannSiegel

/-- `R_{0,N}(s) = (1/8) (s(s-1)/2) π^{-s/2} Γ(s/2) ∫_{N+1/2 ↙} w^{-s} e^{iπw²}/(e^{iπw} - e^{-iπw}) dw`. -/
@[expose] noncomputable def remainder (N : ℕ) (s : ℂ) : ℂ :=
  s * (s - 1) / 16 * Gammaℝ s * rsIntegral s (N + 1 / 2)

/-- `r_{0,n}(s) = (1/8) (s(s-1)/2) π^{-s/2} Γ(s/2) n^{-s}`. -/
@[expose] noncomputable def mainTerm (n : ℕ) (s : ℂ) : ℂ :=
  s * (s - 1) / 16 * Gammaℝ s * (n : ℂ) ^ (-s)

/-! ### The reflection identity for the two coefficients -/

theorem rsOmega_cpow (w : ℂ) : ω ^ w = cexp (π * I / 4 * w) := by
  unfold Complex.rsOmega
  rw [exp_cpow_of_im]
  · simp; linarith [Real.pi_pos]
  · simp; linarith [Real.pi_pos]

theorem Gammaℝ_conj (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj, map_div₀, map_ofNat,
    show -(starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (-s / 2) by
      rw [map_div₀, map_neg, map_ofNat],
    Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm),
    Complex.conj_ofReal]

theorem Gammaℝ_one_sub_ne_zero {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) : Gammaℝ (1 - s) ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n h
  apply hs (2 * n + 1)
  push_cast
  linear_combination -h

/-- `Γ_ℝ(1 - s) e^{-iπs/4} (1 + e^{iπs}) = Γ_ℝ(s) ω^s (2π)^s / Γ(s)` for `s ∉ ℤ`, `Re s > 0`. -/
theorem Gammaℝ_one_sub_mul_eq {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) (hre : 0 < s.re) :
    Gammaℝ (1 - s) * (cexp (-(π * I * s / 4)) * (1 + cexp (π * I * s))) =
      Gammaℝ s * (ω ^ s * (2 * π) ^ s / Complex.Gamma s) := by
  have h1 : ∀ n : ℕ, s ≠ -(2 * n + 1) := fun n h => hs (-(2 * n + 1)) (by rw [h]; push_cast; ring)
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  have hG := Gammaℝ_div_Gammaℝ_one_sub h1
  rw [div_eq_iff (Gammaℝ_one_sub_ne_zero hs), Gammaℂ_def] at hG
  rw [hG, rsOmega_cpow, ← mul_div_cancel_left₀ (Complex.cos (π * s / 2)) two_ne_zero,
    Complex.two_cos, Complex.cpow_neg]
  have h2π : (2 * π : ℂ) ≠ 0 := by
    apply mul_ne_zero two_ne_zero; exact_mod_cast Real.pi_ne_zero
  have hpow : (2 * π : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl h2π
  set E := cexp (π * I * s / 4) with hE
  have e1 : cexp (-(π * I * s / 4)) = E⁻¹ := by rw [hE, ← Complex.exp_neg]
  have e2 : cexp (π * I * s) = E ^ 4 := by
    rw [hE, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : cexp (π * s / 2 * I) = E ^ 2 := by
    rw [hE, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e4 : cexp (-(π * s / 2) * I) = (E ^ 2)⁻¹ := by
    rw [← e3, ← Complex.exp_neg]; congr 1; ring
  have e5 : cexp (π * I / 4 * s) = E := by rw [hE]; congr 1; ring
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  rw [e1, e2, e4, e3, e5]
  field_simp
  ring

/-! ### The formula for `Re s > 2` -/

theorem completedRiemannZeta_eq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)]

theorem conj_one_sub_conj_mul (s : ℂ) :
    (starRingEnd ℂ) ((1 - (starRingEnd ℂ) s) * (1 - (starRingEnd ℂ) s - 1) / 16 *
      Gammaℝ (1 - (starRingEnd ℂ) s)) = s * (s - 1) / 16 * Gammaℝ (1 - s) := by
  have e : 1 - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) := by rw [map_sub, map_one]
  rw [e, Gammaℝ_conj]
  simp only [map_mul, map_div₀, map_sub, map_one, map_ofNat, Complex.conj_conj]
  ring

/-- The Riemann–Siegel formula for `Re s > 2`, `s ∉ ℤ`, with the line through `c ∈ (0, 1)`. -/
theorem formula_of_two_lt_re {s : ℂ} (hs : 2 < s.re) (hsZ : ∀ n : ℤ, s ≠ n) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) :
    s * (s - 1) / 16 * completedRiemannZeta s =
      s * (s - 1) / 16 * Gammaℝ s * rsIntegral s c +
        (starRingEnd ℂ) ((1 - (starRingEnd ℂ) s) * (1 - (starRingEnd ℂ) s - 1) / 16 *
          Gammaℝ (1 - (starRingEnd ℂ) s) * rsIntegral (1 - (starRingEnd ℂ) s) c) := by
  rw [map_mul, conj_one_sub_conj_mul, conj_rsIntegral_one_sub hs hc0 hc1,
    rsIntegral_eq_zeta_sub (by linarith) hc0 hc1, completedRiemannZeta_eq_mul (by linarith)]
  have h := Gammaℝ_one_sub_mul_eq hsZ (by linarith)
  linear_combination (-(s * (s - 1) / 16 * gaussIntegral s)) * h

/-! ### Analytic continuation -/

theorem differentiableAt_Gammaℝ {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) : DifferentiableAt ℂ Gammaℝ s := by
  have : Gammaℝ = fun s : ℂ => (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := funext Gammaℝ_def
  rw [this]
  refine DifferentiableAt.mul ?_ ?_
  · exact (differentiableAt_id.neg.div_const 2).const_cpow
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · refine (Complex.differentiableAt_Gamma _ ?_).comp s (differentiableAt_id.div_const 2)
    intro m h
    apply hs (-2 * m)
    push_cast
    linear_combination 2 * h

theorem differentiableAt_remainder {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) (N : ℕ) :
    DifferentiableAt ℂ (remainder N) s := by
  unfold remainder
  have hc0 : (0 : ℝ) < N + 1 / 2 := by positivity
  have hcZ : ∀ n : ℤ, (N : ℝ) + 1 / 2 ≠ n := by
    intro n h
    have : (2 * N + 1 : ℤ) = 2 * n := by
      have h' : (2 * N + 1 : ℝ) = 2 * n := by linear_combination 2 * h
      exact_mod_cast h'
    omega
  exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).div_const 16).mul
    (differentiableAt_Gammaℝ hs) |>.mul (differentiable_rsIntegral hc0 hcZ s)

theorem conj_ne_int {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) : ∀ n : ℤ, 1 - (starRingEnd ℂ) s ≠ n := by
  intro n h
  apply hs (1 - n)
  have := congrArg (starRingEnd ℂ) h
  rw [map_sub, map_one, Complex.conj_conj, map_intCast] at this
  push_cast
  linear_combination -this

theorem differentiableAt_conj_remainder {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) (N : ℕ) :
    DifferentiableAt ℂ (fun s => (starRingEnd ℂ) (remainder N (1 - (starRingEnd ℂ) s))) s := by
  have h := (differentiableAt_remainder (conj_ne_int hs) N).comp ((starRingEnd ℂ) s)
    ((differentiableAt_const 1).sub differentiableAt_id)
  have h2 := h.conj_conj
  rw [Complex.conj_conj] at h2
  exact h2

/-- **The Riemann–Siegel formula**: for `s ∉ ℤ`,
`ξ(s)/8 = R_{0,0}(s) + conj (R_{0,0}(1 - conj s))`. -/
theorem formula {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) :
    s * (s - 1) / 16 * completedRiemannZeta s =
      remainder 0 s + (starRingEnd ℂ) (remainder 0 (1 - (starRingEnd ℂ) s)) := by
  set U : Set ℂ := (Set.range ((↑) : ℤ → ℂ))ᶜ with hU
  have hUopen : IsOpen U := Complex.isClosed_range_intCast.isOpen_compl
  have hUconn : IsPreconnected U :=
    ((Set.countable_range _).isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_cast)).isPreconnected
  have hmem : ∀ {s : ℂ}, s ∈ U ↔ ∀ n : ℤ, s ≠ n := by
    intro s
    simp only [hU, mem_compl_iff, mem_range, not_exists]
    exact ⟨fun h n hn => h n hn.symm, fun h n hn => h n hn.symm⟩
  have hf : AnalyticOnNhd ℂ (fun s => s * (s - 1) / 16 * completedRiemannZeta s) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUopen
    have hs' := hmem.1 hs
    exact (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).div_const 16).mul
      (differentiableAt_completedZeta (by simpa using hs' 0)
        (by simpa using hs' 1))).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ
      (fun s => remainder 0 s + (starRingEnd ℂ) (remainder 0 (1 - (starRingEnd ℂ) s))) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUopen
    have hs' := hmem.1 hs
    exact ((differentiableAt_remainder hs' 0).add
      (differentiableAt_conj_remainder hs' 0)).differentiableWithinAt
  have h₀ : ((5 / 2 : ℝ) : ℂ) ∈ U := by
    rw [hmem]
    intro n h
    have : (5 : ℝ) / 2 = n := by exact_mod_cast h
    have h2 : (5 : ℤ) = 2 * n := by
      have : (5 : ℝ) = 2 * n := by linarith
      exact_mod_cast this
    omega
  have hV : {s : ℂ | 2 < s.re} ∩ U ∈ 𝓝 ((5 / 2 : ℝ) : ℂ) := by
    refine ((isOpen_lt continuous_const Complex.continuous_re).inter hUopen).mem_nhds ⟨?_, h₀⟩
    simp only [mem_ofPred_eq, Complex.ofReal_re]; norm_num
  have hfg := hf.eqOn_of_preconnected_of_eventuallyEq hg hUconn h₀
    (Filter.eventually_of_mem hV fun s hs => by
      have := formula_of_two_lt_re hs.1 (hmem.1 hs.2) (c := 1 / 2) (by norm_num) (by norm_num)
      simp only [remainder, Nat.cast_zero, zero_add]
      exact this)
  exact hfg (hmem.2 hs)

/-! ### The residue expansion -/

theorem remainder_zero_eq (s : ℂ) (N : ℕ) :
    remainder 0 s = ∑ n ∈ Finset.range N, mainTerm (n + 1) s + remainder N s := by
  unfold remainder mainTerm
  rw [rsIntegral_add_half s N, mul_sub (s * (s - 1) / 16 * Gammaℝ s), Finset.mul_sum,
    Nat.cast_zero, zero_add]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The Riemann–Siegel formula with `N` main terms on each side: for `s ∉ ℤ`,
`ξ(s)/8 = ∑_{n=1}^N r_{0,n}(s) + ∑_{n=1}^N conj (r_{0,n}(1 - conj s)) + R_{0,N}(s)
+ conj (R_{0,N}(1 - conj s))`. -/
theorem formula_expand {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) (N : ℕ) :
    s * (s - 1) / 16 * completedRiemannZeta s =
      ∑ n ∈ Finset.range N, mainTerm (n + 1) s +
        ∑ n ∈ Finset.range N, (starRingEnd ℂ) (mainTerm (n + 1) (1 - (starRingEnd ℂ) s)) +
        remainder N s + (starRingEnd ℂ) (remainder N (1 - (starRingEnd ℂ) s)) := by
  rw [formula hs, remainder_zero_eq s N, remainder_zero_eq (1 - (starRingEnd ℂ) s) N, map_add,
    map_sum]
  ring

end RiemannSiegel
