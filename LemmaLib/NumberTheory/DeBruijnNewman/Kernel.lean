/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Riemann's kernel as `(W'' - W) / 8`

Riemann's kernel `Φ` (`DeBruijnNewman.phi`) is a second-order differential expression in the
much simpler function

`W u = e^u ∑_{m ≥ 1} e^{-π m² e^{4u}} = e^u ω(e^{4u})`,

namely `Φ = (W'' - W) / 8` (`phi_eq`). This file defines `W`, differentiates its series twice
(`hasDerivAt_W`, `hasDerivAt_W'`), and proves the uniform decay estimates on `u ≥ 0`

`‖W u‖, ‖W' u‖, ‖W'' u‖ ≤ C * g u`, `g u = e^{9u} e^{-(π/2) e^{4u}}`,

together with the elementary inequality `exp (t u² + b u) * g u ≤ exp K * exp (-u)`
(`exp_mul_g_le`) that makes every integral against `Φ` on `Ioi 0` absolutely convergent.

These facts drive the identification `H 0 z = ξ((1 + i z)/2) / 8` (two integrations by parts) and
the heat-kernel representation of `H t`.
-/

@[expose] public section

open Real Set Filter Topology

namespace DeBruijnNewman


/-- The `n`-th term `exp (u - π (n+1)² e^{4u})` of the series defining `W`. -/
noncomputable def Wterm (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u - π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))

/-- `W u = e^u ∑_{m ≥ 1} e^{-π m² e^{4u}}`. -/
noncomputable def W (u : ℝ) : ℝ := ∑' n, Wterm n u

/-- Derivative of `Wterm n`. -/
noncomputable def Wterm' (n : ℕ) (u : ℝ) : ℝ :=
  (1 - 4 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)) * Wterm n u

/-- Derivative of `W`. -/
noncomputable def W' (u : ℝ) : ℝ := ∑' n, Wterm' n u

/-- Second derivative of `Wterm n`. -/
noncomputable def Wterm'' (n : ℕ) (u : ℝ) : ℝ :=
  (1 - 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
    + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) * Wterm n u

/-- Second derivative of `W`. -/
noncomputable def W'' (u : ℝ) : ℝ := ∑' n, Wterm'' n u

lemma Wterm_pos (n : ℕ) (u : ℝ) : 0 < Wterm n u := Real.exp_pos _

lemma hasDerivAt_exp_const_mul (c u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (c * u)) (c * Real.exp (c * u)) u := by
  have := ((hasDerivAt_id u).const_mul c).exp
  simpa [mul_comm] using this

lemma hasDerivAt_Wterm (n : ℕ) (u : ℝ) : HasDerivAt (Wterm n) (Wterm' n u) u := by
  have h1 : HasDerivAt (fun u : ℝ => u - π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))
      (1 - π * ((n : ℝ) + 1) ^ 2 * (4 * Real.exp (4 * u))) u :=
    (hasDerivAt_id u).sub ((hasDerivAt_exp_const_mul 4 u).const_mul _)
  have h2 := h1.exp
  have : Wterm n = fun u => Real.exp (u - π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)) := rfl
  rw [this]
  convert h2 using 1
  simp only [Wterm', Wterm]
  ring

lemma hasDerivAt_Wterm' (n : ℕ) (u : ℝ) : HasDerivAt (Wterm' n) (Wterm'' n u) u := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - 4 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))
      (0 - 4 * π * ((n : ℝ) + 1) ^ 2 * (4 * Real.exp (4 * u))) u :=
    (hasDerivAt_const u 1).sub ((hasDerivAt_exp_const_mul 4 u).const_mul _)
  refine (h1.mul (hasDerivAt_Wterm n u)).congr_deriv ?_
  simp only [Wterm'', Wterm']
  have : Real.exp (8 * u) = Real.exp (4 * u) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this]
  ring

/-- Summability of `(n+1)^k exp (-c (n+1)^2)`. -/
lemma summable_pow_mul_exp_neg_sq (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * Real.exp (-c * ((n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul k hc)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
  push_cast
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have h1 : (n:ℝ) + 1 ≤ ((n:ℝ) + 1) ^ 2 := by nlinarith [(by positivity : (0:ℝ) ≤ n)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]


/-- The decay rate used in uniform bounds on `|u| < R`. -/
noncomputable def rate (R : ℝ) : ℝ := π * Real.exp (-(4 * R))

lemma rate_pos (R : ℝ) : 0 < rate R := by unfold rate; positivity

lemma Wterm_le {R u : ℝ} (hu : u ∈ Ioo (-R) R) (n : ℕ) :
    Wterm n u ≤ Real.exp R * Real.exp (-rate R * ((n : ℝ) + 1) ^ 2) := by
  unfold Wterm rate
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : Real.exp (-(4 * R)) ≤ Real.exp (4 * u) := Real.exp_le_exp.mpr (by linarith [hu.1])
  have h2 : 0 ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
  nlinarith [hu.2, mul_le_mul_of_nonneg_left h1 h2]

lemma norm_Wterm_le {R u : ℝ} (hu : u ∈ Ioo (-R) R) (n : ℕ) :
    ‖Wterm n u‖ ≤ Real.exp R * Real.exp (-rate R * ((n : ℝ) + 1) ^ 2) := by
  rw [Real.norm_eq_abs, abs_of_pos (Wterm_pos n u)]
  exact Wterm_le hu n

lemma norm_Wterm'_le {R u : ℝ} (hu : u ∈ Ioo (-R) R) (n : ℕ) :
    ‖Wterm' n u‖ ≤ (1 + 4 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * R)) *
      (Real.exp R * Real.exp (-rate R * ((n : ℝ) + 1) ^ 2)) := by
  unfold Wterm'
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Wterm_pos n u)]
  refine mul_le_mul ?_ (Wterm_le hu n) (Wterm_pos n u).le (by positivity)
  have h1 : Real.exp (4 * u) ≤ Real.exp (4 * R) := Real.exp_le_exp.mpr (by linarith [hu.2])
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * π * ((n : ℝ) + 1) ^ 2)
  have h3 : 0 ≤ 4 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) := by positivity
  rw [abs_le]
  constructor <;> nlinarith

lemma norm_Wterm''_le {R u : ℝ} (hu : u ∈ Ioo (-R) R) (n : ℕ) :
    ‖Wterm'' n u‖ ≤ (1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * R)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * R)) *
      (Real.exp R * Real.exp (-rate R * ((n : ℝ) + 1) ^ 2)) := by
  unfold Wterm''
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Wterm_pos n u)]
  refine mul_le_mul ?_ (Wterm_le hu n) (Wterm_pos n u).le (by positivity)
  have h1 : Real.exp (4 * u) ≤ Real.exp (4 * R) := Real.exp_le_exp.mpr (by linarith [hu.2])
  have h1' : Real.exp (8 * u) ≤ Real.exp (8 * R) := Real.exp_le_exp.mpr (by linarith [hu.2])
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 24 * π * ((n : ℝ) + 1) ^ 2)
  have h2' := mul_le_mul_of_nonneg_left h1'
    (by positivity : (0:ℝ) ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4)
  have h3 : 0 ≤ 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) := by positivity
  have h3' : 0 ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u) := by positivity
  rw [abs_le]
  constructor <;> nlinarith

lemma summable_bound₀ (R : ℝ) :
    Summable fun n : ℕ => Real.exp R * Real.exp (-rate R * ((n : ℝ) + 1) ^ 2) := by
  have := (summable_pow_mul_exp_neg_sq 0 (rate_pos R)).mul_left (Real.exp R)
  simpa using this

lemma summable_bound₁ (R : ℝ) :
    Summable fun n : ℕ => (1 + 4 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * R)) *
      (Real.exp R * Real.exp (-rate R * ((n : ℝ) + 1) ^ 2)) := by
  have h2 := (summable_pow_mul_exp_neg_sq 2 (rate_pos R)).mul_left
    (4 * π * Real.exp (4 * R) * Real.exp R)
  convert (summable_bound₀ R).add h2 using 1
  ext n
  ring

lemma summable_bound₂ (R : ℝ) :
    Summable fun n : ℕ => (1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * R)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * R)) *
      (Real.exp R * Real.exp (-rate R * ((n : ℝ) + 1) ^ 2)) := by
  have h2 := (summable_pow_mul_exp_neg_sq 2 (rate_pos R)).mul_left
    (24 * π * Real.exp (4 * R) * Real.exp R)
  have h4 := (summable_pow_mul_exp_neg_sq 4 (rate_pos R)).mul_left
    (16 * π ^ 2 * Real.exp (8 * R) * Real.exp R)
  convert ((summable_bound₀ R).add h2).add h4 using 1
  ext n
  ring

lemma mem_Ioo_abs_add_one (u : ℝ) : u ∈ Ioo (-(|u| + 1)) (|u| + 1) := by
  constructor <;> linarith [le_abs_self u, neg_abs_le u]

lemma summable_Wterm (u : ℝ) : Summable fun n => Wterm n u :=
  (summable_bound₀ (|u| + 1)).of_norm_bounded (fun n => norm_Wterm_le (mem_Ioo_abs_add_one u) n)

lemma summable_Wterm' (u : ℝ) : Summable fun n => Wterm' n u :=
  (summable_bound₁ (|u| + 1)).of_norm_bounded (fun n => norm_Wterm'_le (mem_Ioo_abs_add_one u) n)

lemma summable_Wterm'' (u : ℝ) : Summable fun n => Wterm'' n u :=
  (summable_bound₂ (|u| + 1)).of_norm_bounded
    (fun n => norm_Wterm''_le (mem_Ioo_abs_add_one u) n)

lemma hasDerivAt_W (u : ℝ) : HasDerivAt W (W' u) u := by
  have := hasDerivAt_tsum_of_isPreconnected (summable_bound₁ (|u| + 1)) isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => hasDerivAt_Wterm n y)
    (fun n y hy => norm_Wterm'_le hy n) (mem_Ioo_abs_add_one u) (summable_Wterm u)
    (mem_Ioo_abs_add_one u)
  exact this

lemma hasDerivAt_W' (u : ℝ) : HasDerivAt W' (W'' u) u := by
  have := hasDerivAt_tsum_of_isPreconnected (summable_bound₂ (|u| + 1)) isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => hasDerivAt_Wterm' n y)
    (fun n y hy => norm_Wterm''_le hy n) (mem_Ioo_abs_add_one u) (summable_Wterm' u)
    (mem_Ioo_abs_add_one u)
  exact this

@[fun_prop]
lemma continuous_W : Continuous W :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_W u).continuousAt

@[fun_prop]
lemma continuous_W' : Continuous W' :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_W' u).continuousAt

lemma continuous_Wterm'' (n : ℕ) : Continuous (Wterm'' n) := by
  unfold Wterm'' Wterm; fun_prop

@[fun_prop]
lemma continuous_W'' : Continuous W'' := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have : ContinuousOn W'' (Ioo (-(|u| + 1)) (|u| + 1)) :=
    continuousOn_tsum (fun n => (continuous_Wterm'' n).continuousOn) (summable_bound₂ _)
      (fun n y hy => norm_Wterm''_le hy n)
  exact this.continuousAt (Ioo_mem_nhds (mem_Ioo_abs_add_one u).1 (mem_Ioo_abs_add_one u).2)

lemma phi_eq (u : ℝ) : phi u = (W'' u - W u) / 8 := by
  unfold phi W'' W
  rw [← (summable_Wterm'' u).tsum_sub (summable_Wterm u), ← tsum_div_const]
  congr 1
  ext n
  dsimp only
  simp only [Wterm'', Wterm]
  push_cast
  have e9 : Real.exp (9 * u) = Real.exp (8 * u) * Real.exp u := by rw [← Real.exp_add]; ring_nf
  have e5 : Real.exp (5 * u) = Real.exp (4 * u) * Real.exp u := by rw [← Real.exp_add]; ring_nf
  have es : Real.exp (u - π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)) =
      Real.exp u * Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))) := by
    rw [← Real.exp_add]; ring_nf
  rw [e9, e5, es]
  ring

/-! ### Decay for `u ≥ 0` -/

/-- The dominating function `e^{9u} e^{-(π/2) e^{4u}}`. -/
noncomputable def g (u : ℝ) : ℝ := Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))

lemma g_pos (u : ℝ) : 0 < g u := by unfold g; positivity

/-- Polynomial weight in the termwise bounds. -/
noncomputable def P (n : ℕ) : ℝ :=
  1 + 24 * π * ((n : ℝ) + 1) ^ 2 + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4

lemma one_le_P (n : ℕ) : 1 ≤ P n := by
  unfold P
  linarith [(by positivity : (0:ℝ) ≤ 24 * π * ((n : ℝ) + 1) ^ 2),
    (by positivity : (0:ℝ) ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4)]

/-- The weight `P n * exp (-(π/2) (n+1)^2)`. -/
noncomputable def wt (n : ℕ) : ℝ := P n * Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2)

lemma wt_pos (n : ℕ) : 0 < wt n :=
  mul_pos (lt_of_lt_of_le one_pos (one_le_P n)) (Real.exp_pos _)

lemma summable_wt : Summable wt := by
  have h0 := summable_pow_mul_exp_neg_sq 0 (by positivity : (0:ℝ) < π / 2)
  have h2 := (summable_pow_mul_exp_neg_sq 2 (by positivity : (0:ℝ) < π / 2)).mul_left (24 * π)
  have h4 := (summable_pow_mul_exp_neg_sq 4 (by positivity : (0:ℝ) < π / 2)).mul_left
    (16 * π ^ 2)
  convert (h0.add h2).add h4 using 1
  ext n
  simp only [wt, P]
  ring

/-- The constant `C = ∑ wt n`. -/
noncomputable def C : ℝ := ∑' n, wt n

lemma Wterm_le_of_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    Wterm n u ≤ Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * (Real.exp u *
      Real.exp (-(π / 2) * Real.exp (4 * u))) := by
  unfold Wterm
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : 1 ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  have h2 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(by positivity : (0:ℝ) ≤ n)]
  have h3 : 0 ≤ (((n : ℝ) + 1) ^ 2 - 1) * (Real.exp (4 * u) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have h4 : 1 ≤ ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) := by nlinarith
  nlinarith [mul_nonneg pi_pos.le h3, mul_le_mul_of_nonneg_left h4 pi_pos.le]

lemma exp_mul_le_g {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) *
      (Real.exp u * Real.exp (-(π / 2) * Real.exp (4 * u))) ≤ P n * g u := by
  unfold P g
  have h4 : Real.exp (4 * u) ≤ Real.exp (8 * u) := Real.exp_le_exp.mpr (by linarith)
  have h1 : 1 ≤ Real.exp (8 * u) := Real.one_le_exp (by linarith)
  have e9 : Real.exp (9 * u) = Real.exp (8 * u) * Real.exp u := by rw [← Real.exp_add]; ring_nf
  rw [e9]
  have hpos : 0 < Real.exp u * Real.exp (-(π / 2) * Real.exp (4 * u)) := by positivity
  have : (1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) ≤
      (1 + 24 * π * ((n : ℝ) + 1) ^ 2 + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4) * Real.exp (8 * u) := by
    nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 24 * π * ((n : ℝ) + 1) ^ 2),
      (by positivity : (0:ℝ) ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4)]
  calc _ ≤ (1 + 24 * π * ((n : ℝ) + 1) ^ 2 + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4) * Real.exp (8 * u) *
      (Real.exp u * Real.exp (-(π / 2) * Real.exp (4 * u))) :=
        mul_le_mul_of_nonneg_right this hpos.le
    _ = _ := by ring

lemma norm_Wterm_le_wt_mul_g {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : ‖Wterm n u‖ ≤ wt n * g u := by
  rw [Real.norm_eq_abs, abs_of_pos (Wterm_pos n u)]
  have h1 := Wterm_le_of_nonneg hu n
  have h2 := exp_mul_le_g hu n
  have h3 : 1 ≤ 1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u) := by
    nlinarith [(by positivity : (0:ℝ) ≤ 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)),
      (by positivity : (0:ℝ) ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u))]
  have hpos : 0 < Real.exp u * Real.exp (-(π / 2) * Real.exp (4 * u)) := by positivity
  have hw : 0 < Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) := Real.exp_pos _
  unfold wt
  calc Wterm n u ≤ Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * (Real.exp u *
      Real.exp (-(π / 2) * Real.exp (4 * u))) := h1
    _ ≤ Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * ((1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) *
      (Real.exp u * Real.exp (-(π / 2) * Real.exp (4 * u)))) := by
        apply mul_le_mul_of_nonneg_left _ hw.le
        exact le_mul_of_one_le_left hpos.le h3
    _ ≤ Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * (P n * g u) := mul_le_mul_of_nonneg_left h2 hw.le
    _ = _ := by ring

lemma norm_Wterm'_le_wt_mul_g {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : ‖Wterm' n u‖ ≤ wt n * g u := by
  unfold Wterm'
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Wterm_pos n u)]
  have h1 := Wterm_le_of_nonneg hu n
  have h2 := exp_mul_le_g hu n
  have h3 : |1 - 4 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)| ≤
      1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u) := by
    rw [abs_le]
    constructor <;> nlinarith [(by positivity : (0:ℝ) ≤ 4 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)),
      (by positivity : (0:ℝ) ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u))]
  have hw : 0 < Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) := Real.exp_pos _
  unfold wt
  calc _ ≤ (1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) *
        (Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * (Real.exp u *
          Real.exp (-(π / 2) * Real.exp (4 * u)))) :=
        mul_le_mul h3 h1 (Wterm_pos n u).le (by positivity)
    _ = Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * ((1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) *
      (Real.exp u * Real.exp (-(π / 2) * Real.exp (4 * u)))) := by ring
    _ ≤ Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * (P n * g u) := mul_le_mul_of_nonneg_left h2 hw.le
    _ = _ := by ring

lemma norm_Wterm''_le_wt_mul_g {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : ‖Wterm'' n u‖ ≤ wt n * g u := by
  unfold Wterm''
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Wterm_pos n u)]
  have h1 := Wterm_le_of_nonneg hu n
  have h2 := exp_mul_le_g hu n
  have h3 : |1 - 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)| ≤
      1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u) := by
    rw [abs_le]
    constructor <;> nlinarith [(by positivity : (0:ℝ) ≤ 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)),
      (by positivity : (0:ℝ) ≤ 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u))]
  have hw : 0 < Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) := Real.exp_pos _
  unfold wt
  calc _ ≤ (1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) *
        (Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * (Real.exp u *
          Real.exp (-(π / 2) * Real.exp (4 * u)))) :=
        mul_le_mul h3 h1 (Wterm_pos n u).le (by positivity)
    _ = Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * ((1 + 24 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)
        + 16 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (8 * u)) *
      (Real.exp u * Real.exp (-(π / 2) * Real.exp (4 * u)))) := by ring
    _ ≤ Real.exp (-(π / 2) * ((n : ℝ) + 1) ^ 2) * (P n * g u) := mul_le_mul_of_nonneg_left h2 hw.le
    _ = _ := by ring

lemma norm_tsum_le_C_mul_g {F : ℕ → ℝ → ℝ} (hF : ∀ u, Summable fun n => F n u)
    (hb : ∀ n, ∀ u, 0 ≤ u → ‖F n u‖ ≤ wt n * g u) {u : ℝ} (hu : 0 ≤ u) :
    ‖∑' n, F n u‖ ≤ C * g u := by
  calc ‖∑' n, F n u‖ ≤ ∑' n, ‖F n u‖ := norm_tsum_le_tsum_norm (hF u).norm
    _ ≤ ∑' n, wt n * g u :=
        (hF u).norm.tsum_le_tsum (fun n => hb n u hu) (summable_wt.mul_right _)
    _ = C * g u := by rw [tsum_mul_right]; rfl

lemma norm_W_le {u : ℝ} (hu : 0 ≤ u) : ‖W u‖ ≤ C * g u :=
  norm_tsum_le_C_mul_g summable_Wterm (fun n _ hu => norm_Wterm_le_wt_mul_g hu n) hu

lemma norm_W'_le {u : ℝ} (hu : 0 ≤ u) : ‖W' u‖ ≤ C * g u :=
  norm_tsum_le_C_mul_g summable_Wterm' (fun n _ hu => norm_Wterm'_le_wt_mul_g hu n) hu

lemma norm_W''_le {u : ℝ} (hu : 0 ≤ u) : ‖W'' u‖ ≤ C * g u :=
  norm_tsum_le_C_mul_g summable_Wterm'' (fun n _ hu => norm_Wterm''_le_wt_mul_g hu n) hu

/-- The key decay estimate: `e^{t u² + b u} g u ≤ e^{K} e^{-u}` for `u ≥ 0`. -/
lemma exp_mul_g_le {t b : ℝ} (ht : 0 ≤ t) (hb : 0 ≤ b) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (t * u ^ 2 + b * u) * g u ≤
      Real.exp ((t + b + 10) ^ 2 / (2 * π)) * Real.exp (-u) := by
  unfold g
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hy : u ≤ Real.exp (2 * u) := by
    have := Real.add_one_le_exp u
    have h2 : Real.exp u ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hy2 : u ^ 2 ≤ Real.exp (2 * u) := by
    have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have : u ^ 2 ≤ Real.exp u ^ 2 := by nlinarith
    rw [← Real.exp_nat_mul] at *
    simpa using this
  have e4 : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e4]
  set y := Real.exp (2 * u)
  have hK : (t + b + 10) * y - π / 2 * y ^ 2 ≤ (t + b + 10) ^ 2 / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (π * y - (t + b + 10))]
  nlinarith [mul_le_mul_of_nonneg_left hy2 ht, mul_le_mul_of_nonneg_left hy hb]

end DeBruijnNewman
