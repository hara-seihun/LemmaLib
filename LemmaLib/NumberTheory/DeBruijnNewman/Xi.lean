/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.Theta
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-!
# `H 0 z = ξ((1 + i z)/2) / 8`

This file proves Riemann's integral representation of the completed zeta function in de Bruijn's
normalisation: for every complex `z`,

`H 0 z = 1/16 - (1 + z²)/64 · completedRiemannZeta₀ ((1 + i z)/2)` (`H_zero_eq`),

equivalently `H 0 z = ξ((1 + i z)/2) / 8` with `ξ(s) = s(s-1)/2 · Λ(s)` away from the poles of `Λ`
(`H_zero_eq_xi`).

The proof integrates by parts twice. With `Φ = (W'' - W)/8` (`phi_eq`),

`∫₀^∞ Φ(u) cos(zu) du = (1/8) (-W'(0) - (1 + z²) ∫₀^∞ W(u) cos(zu) du)`,

the boundary value is `W'(0) = -1/2` (`W'_zero`), and the remaining integral is Riemann's
representation of `Λ₀` (`completedRiemannZeta₀_eq_integral`). No analytic continuation is needed:
both sides are computed directly for every `z`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace DeBruijnNewman


lemma C_nonneg : 0 ≤ C := tsum_nonneg fun n => (wt_pos n).le

lemma norm_cos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h := Complex.two_cos w
  have h1 : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (-w * Complex.I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; simp
  have h3 : ‖2 * Complex.cos w‖ ≤ Real.exp (-w.im) + Real.exp w.im := by
    rw [h]; exact (norm_add_le _ _).trans (by rw [h1, h2])
  rw [norm_mul, Complex.norm_two] at h3
  have e1 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  have e2 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self _)
  linarith

lemma norm_sin_le (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have h := Complex.two_sin w
  have h1 : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (-w * Complex.I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; simp
  have h3 : ‖2 * Complex.sin w‖ ≤ Real.exp w.im + Real.exp (-w.im) := by
    rw [h, norm_mul, Complex.norm_I, mul_one]
    exact (norm_sub_le _ _).trans (by rw [h1, h2])
  rw [norm_mul, Complex.norm_two] at h3
  have e1 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  have e2 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self _)
  linarith

lemma norm_cos_mul_le' (z : ℂ) (u : ℝ) : ‖Complex.cos (z * u)‖ ≤ Real.exp (|z.im| * |u|) := by
  refine (norm_cos_le _).trans (le_of_eq ?_)
  congr 1
  simp [abs_mul]

lemma norm_cos_mul_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.cos (z * u)‖ ≤ Real.exp (|z.im| * u) := by
  simpa [abs_of_nonneg hu] using norm_cos_mul_le' z u

lemma norm_sin_mul_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.sin (z * u)‖ ≤ Real.exp (|z.im| * u) := by
  refine (norm_sin_le _).trans (le_of_eq ?_)
  congr 1
  simp [abs_mul, abs_of_nonneg hu]

/-- The decay constant `exp ((t + b + 10)^2 / (2π))`. -/
noncomputable def K (t b : ℝ) : ℝ := Real.exp ((t + b + 10) ^ 2 / (2 * π))

lemma norm_mul_le_exp_neg {t b u : ℝ} (ht : 0 ≤ t) (hb : 0 ≤ b) (hu : 0 ≤ u) {F : ℝ}
    (hF : ‖F‖ ≤ C * g u) {T : ℂ} (hT : ‖T‖ ≤ Real.exp (t * u ^ 2 + b * u)) :
    ‖T * (F : ℂ)‖ ≤ C * K t b * Real.exp (-u) := by
  rw [norm_mul, Complex.norm_real]
  have h := exp_mul_g_le ht hb hu
  calc ‖T‖ * ‖F‖ ≤ Real.exp (t * u ^ 2 + b * u) * (C * g u) :=
        mul_le_mul hT hF (norm_nonneg _) (Real.exp_pos _).le
    _ = C * (Real.exp (t * u ^ 2 + b * u) * g u) := by ring
    _ ≤ C * (K t b * Real.exp (-u)) := mul_le_mul_of_nonneg_left h C_nonneg
    _ = _ := by ring

/-- Continuous functions dominated by `A e^{-u}` on `u ≥ 0` are integrable on `Ioi 0`. -/
lemma integrableOn_Ioi_of_le_exp_neg {E : Type*} [NormedAddCommGroup E] {F : ℝ → E}
    (hF : Continuous F) {A : ℝ}
    (h : ∀ u, 0 ≤ u → ‖F u‖ ≤ A * Real.exp (-u)) : IntegrableOn F (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul A)
    hF.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact h u (le_of_lt hu)

lemma tendsto_atTop_of_le_exp_neg {F : ℝ → ℂ} {A : ℝ}
    (h : ∀ u, 0 ≤ u → ‖F u‖ ≤ A * Real.exp (-u)) : Tendsto F atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun u => A * Real.exp (-u)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with u hu using h u hu
  · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul A

lemma hasDerivAt_cos_mul (z : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.cos (z * x)) (-Complex.sin (z * x) * z) x := by
  have h : HasDerivAt (fun w : ℂ => Complex.cos (z * w)) (-Complex.sin (z * x) * z) x := by
    have := (Complex.hasDerivAt_cos (z * x)).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).const_mul z)
    exact this.congr_deriv (by simp)
  exact h.comp_ofReal

lemma hasDerivAt_sin_mul (z : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.sin (z * x)) (Complex.cos (z * x) * z) x := by
  have h : HasDerivAt (fun w : ℂ => Complex.sin (z * w)) (Complex.cos (z * x) * z) x := by
    have := (Complex.hasDerivAt_sin (z * x)).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).const_mul z)
    exact this.congr_deriv (by simp)
  exact h.comp_ofReal

/-! ### Integrability of the integrands -/

lemma integrableOn_W_mul_cos (z : ℂ) :
    IntegrableOn (fun u : ℝ => Complex.cos (z * u) * (W u : ℂ)) (Ioi 0) := by
  refine integrableOn_Ioi_of_le_exp_neg (by fun_prop) (A := C * K 0 |z.im|) fun u hu => ?_
  refine norm_mul_le_exp_neg le_rfl (abs_nonneg _) hu (norm_W_le hu) ?_
  simpa using norm_cos_mul_le z hu

lemma integrableOn_W'_mul_sin (z : ℂ) :
    IntegrableOn (fun u : ℝ => Complex.sin (z * u) * (W' u : ℂ)) (Ioi 0) := by
  refine integrableOn_Ioi_of_le_exp_neg (by fun_prop) (A := C * K 0 |z.im|) fun u hu => ?_
  refine norm_mul_le_exp_neg le_rfl (abs_nonneg _) hu (norm_W'_le hu) ?_
  simpa using norm_sin_mul_le z hu

lemma integrableOn_W''_mul_cos (z : ℂ) :
    IntegrableOn (fun u : ℝ => Complex.cos (z * u) * (W'' u : ℂ)) (Ioi 0) := by
  refine integrableOn_Ioi_of_le_exp_neg (by fun_prop) (A := C * K 0 |z.im|) fun u hu => ?_
  refine norm_mul_le_exp_neg le_rfl (abs_nonneg _) hu (norm_W''_le hu) ?_
  simpa using norm_cos_mul_le z hu

lemma tendsto_cos_mul_W' (z : ℂ) :
    Tendsto (fun u : ℝ => Complex.cos (z * u) * (W' u : ℂ)) atTop (𝓝 0) := by
  refine tendsto_atTop_of_le_exp_neg (A := C * K 0 |z.im|) fun u hu => ?_
  refine norm_mul_le_exp_neg le_rfl (abs_nonneg _) hu (norm_W'_le hu) ?_
  simpa using norm_cos_mul_le z hu

lemma tendsto_sin_mul_W (z : ℂ) :
    Tendsto (fun u : ℝ => Complex.sin (z * u) * (W u : ℂ)) atTop (𝓝 0) := by
  refine tendsto_atTop_of_le_exp_neg (A := C * K 0 |z.im|) fun u hu => ?_
  refine norm_mul_le_exp_neg le_rfl (abs_nonneg _) hu (norm_W_le hu) ?_
  simpa using norm_sin_mul_le z hu

/-! ### Integration by parts -/

/-- First integration by parts:
`∫₀^∞ cos(zu) W''(u) du = -W'(0) + z ∫₀^∞ sin(zu) W'(u) du`. -/
lemma integral_cos_mul_W'' (z : ℂ) :
    ∫ u : ℝ in Ioi 0, Complex.cos (z * u) * (W'' u : ℂ) =
      -(W' 0 : ℂ) + z * ∫ u : ℝ in Ioi 0, Complex.sin (z * u) * (W' u : ℂ) := by
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := (W' 0 : ℂ)) (b' := 0)
    (u := fun x : ℝ => Complex.cos (z * x)) (u' := fun x => -Complex.sin (z * x) * z)
    (v := fun x : ℝ => (W' x : ℂ)) (v' := fun x => (W'' x : ℂ))
    (fun x _ => hasDerivAt_cos_mul z x) (fun x _ => (hasDerivAt_W' x).ofReal_comp)
    (integrableOn_W''_mul_cos z) ?_ ?_ (tendsto_cos_mul_W' z)
  · rw [h, ← integral_const_mul]
    have : ∫ x : ℝ in Ioi 0, -Complex.sin (z * x) * z * (W' x : ℂ) =
        -∫ a : ℝ in Ioi 0, z * (Complex.sin (z * a) * (W' a : ℂ)) := by
      rw [← integral_neg]
      congr 1
      ext x
      ring
    rw [this]
    ring
  · have : IntegrableOn (fun u : ℝ => -z * (Complex.sin (z * u) * (W' u : ℂ))) (Ioi 0) :=
      (integrableOn_W'_mul_sin z).const_mul _
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  · have hc : Continuous (fun x : ℝ => Complex.cos (z * x) * (W' x : ℂ)) := by fun_prop
    have h0 : Tendsto (fun x : ℝ => Complex.cos (z * x) * (W' x : ℂ)) (𝓝[>] 0) (𝓝 (W' 0)) := by
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    exact h0

/-- Second integration by parts:
`∫₀^∞ sin(zu) W'(u) du = -z ∫₀^∞ cos(zu) W(u) du`. -/
lemma integral_sin_mul_W' (z : ℂ) :
    ∫ u : ℝ in Ioi 0, Complex.sin (z * u) * (W' u : ℂ) =
      -z * ∫ u : ℝ in Ioi 0, Complex.cos (z * u) * (W u : ℂ) := by
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun x : ℝ => Complex.sin (z * x)) (u' := fun x => Complex.cos (z * x) * z)
    (v := fun x : ℝ => (W x : ℂ)) (v' := fun x => (W' x : ℂ))
    (fun x _ => hasDerivAt_sin_mul z x) (fun x _ => (hasDerivAt_W x).ofReal_comp)
    (integrableOn_W'_mul_sin z) ?_ ?_ (tendsto_sin_mul_W z)
  · rw [h, neg_mul, ← integral_const_mul]
    rw [show ∫ x : ℝ in Ioi 0, Complex.cos (z * x) * z * (W x : ℂ) =
        ∫ a : ℝ in Ioi 0, z * (Complex.cos (z * a) * (W a : ℂ)) by congr 1; ext x; ring]
    simp only [zero_sub, sub_zero]
  · have : IntegrableOn (fun u : ℝ => z * (Complex.cos (z * u) * (W u : ℂ))) (Ioi 0) :=
      (integrableOn_W_mul_cos z).const_mul _
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  · have hc : Continuous (fun x : ℝ => Complex.sin (z * x) * (W x : ℂ)) := by fun_prop
    have h0 : Tendsto (fun x : ℝ => Complex.sin (z * x) * (W x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    exact h0

/-- `∫₀^∞ cos(zu) W''(u) du = -W'(0) - z² ∫₀^∞ cos(zu) W(u) du`. -/
lemma integral_cos_mul_W''_eq (z : ℂ) :
    ∫ u : ℝ in Ioi 0, Complex.cos (z * u) * (W'' u : ℂ) =
      -(W' 0 : ℂ) - z ^ 2 * ∫ u : ℝ in Ioi 0, Complex.cos (z * u) * (W u : ℂ) := by
  rw [integral_cos_mul_W'', integral_sin_mul_W']
  ring

/-! ### `H 0` and the completed zeta function -/

/-- Riemann's integral representation in de Bruijn's normalisation:
`H 0 z = 1/16 - (1 + z²)/64 · Λ₀((1 + i z)/2)`, where `Λ₀ = completedRiemannZeta₀` is the entire
function `Λ(s) + 1/s + 1/(1 - s)`. This form is valid for every complex `z`, including
`z = ± i` where `Λ` itself has poles. -/
theorem H_zero_eq (z : ℂ) :
    H 0 z = 1 / 16 - (1 + z ^ 2) / 64 * completedRiemannZeta₀ ((1 + Complex.I * z) / 2) := by
  have h1 : H 0 z = ∫ u : ℝ in Ioi 0, ((phi u : ℝ) : ℂ) * Complex.cos (z * u) := by
    unfold H; simp
  rw [h1]
  have h2 : ∀ u : ℝ, ((phi u : ℝ) : ℂ) * Complex.cos (z * u) =
      (1 / 8 : ℂ) * (Complex.cos (z * u) * (W'' u : ℂ) - Complex.cos (z * u) * (W u : ℂ)) := by
    intro u; rw [phi_eq]; push_cast; ring
  simp_rw [h2]
  rw [integral_const_mul, integral_sub (integrableOn_W''_mul_cos z) (integrableOn_W_mul_cos z),
    integral_cos_mul_W''_eq, W'_zero, completedRiemannZeta₀_eq_integral]
  push_cast
  ring

/-- `H 0 z = ξ((1 + i z)/2) / 8` with `ξ(s) = s (s - 1) / 2 · Λ(s)`, for `z ≠ ± i` (the two points
where `Λ` has its poles). -/
theorem H_zero_eq_xi {z : ℂ} (hz : z ≠ Complex.I) (hz' : z ≠ -Complex.I) :
    H 0 z = ((1 + Complex.I * z) / 2 * ((1 + Complex.I * z) / 2 - 1) / 2 *
      completedRiemannZeta ((1 + Complex.I * z) / 2)) / 8 := by
  set s : ℂ := (1 + Complex.I * z) / 2 with hs
  have hs0 : s ≠ 0 := by
    intro h
    apply hz
    have : Complex.I * z = -1 := by
      have := congrArg (fun w => 2 * w) h
      simp only [hs] at this
      linear_combination this
    calc z = -Complex.I * (Complex.I * z) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
      _ = Complex.I := by rw [this]; ring
  have hs1 : s - 1 ≠ 0 := by
    intro h
    apply hz'
    have : Complex.I * z = 1 := by
      have := congrArg (fun w => 2 * w) h
      simp only [hs] at this
      linear_combination this
    calc z = -Complex.I * (Complex.I * z) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
      _ = -Complex.I := by rw [this]; ring
  rw [H_zero_eq, completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  field_simp
  rw [hs]
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  ring_nf
  simp only [Complex.I_sq, hI3]
  ring

end DeBruijnNewman
