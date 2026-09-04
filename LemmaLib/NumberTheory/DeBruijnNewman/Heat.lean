/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import LemmaLib.NumberTheory.DeBruijnNewman.Xi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The heat-kernel representation of `H t`

For `t ≥ 0` the de Bruijn–Newman function is the Gaussian average of `H 0`:

`H t z = ∫ H 0 (z - 2 i √t v) e^{-v²}/√π dv` (`H_eq_integral_H_zero`).

The proof is Fubini applied to the Gaussian identity
`e^{t u²} cos(z u) = ∫ cos((z - 2 i √t v) u) e^{-v²}/√π dv` (`exp_mul_cos_eq_integral`),
with the integrand dominated by `‖Φ(u)‖ e^{2 t u² + |Im z| |u|} · e^{-v²/2}/√π`
(`norm_integrand_le`).

Combined with `H_zero_eq` this expresses `H t` through the completed zeta function
(`H_eq_integral_completedRiemannZeta₀`): with `s = (1 + i z)/2`,

`H t z = ∫ (1/16 - (1 + (z - 2 i √t v)²)/64 · Λ₀(s + √t v)) e^{-v²}/√π dv`,

which is the starting point of Polymath15's analysis of `H t`.
-/

public section

open Real Set Filter Topology MeasureTheory

namespace DeBruijnNewman


/-- The Gaussian weight `e^{-v²}/√π`. -/
@[expose] noncomputable def gauss (v : ℝ) : ℝ := Real.exp (-v ^ 2) / Real.sqrt π

@[fun_prop]
lemma continuous_gauss : Continuous gauss := by unfold gauss; fun_prop

lemma ofReal_sqrt_pi : ((Real.sqrt π : ℝ) : ℂ) = (π : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow pi_pos.le]
  push_cast
  rfl

lemma integral_cexp_neg_sq_add_mul (c : ℂ) :
    ∫ v : ℝ, Complex.exp (-(v : ℂ) ^ 2 + c * v) = (Real.sqrt π : ℂ) * Complex.exp (c ^ 2 / 4) := by
  have := integral_cexp_quadratic (b := -1) (by simp) c 0
  rw [ofReal_sqrt_pi]
  rw [show c ^ 2 / 4 = 0 - c ^ 2 / (4 * -1) by ring, show (π : ℂ) = π / -(-1) by ring, ← this]
  congr 1
  ext v
  ring_nf

lemma integrable_cexp_neg_sq_add_mul (c : ℂ) :
    Integrable fun v : ℝ => Complex.exp (-(v : ℂ) ^ 2 + c * v) := by
  have := integrable_cexp_quadratic' (b := -1) (by simp) c 0
  refine this.congr (Eventually.of_forall fun v => ?_)
  simp only
  ring_nf

/-- `e^{t u²} cos(z u) = ∫ cos((z - 2i√t v) u) e^{-v²}/√π dv`. -/
lemma exp_mul_cos_eq_integral {t : ℝ} (ht : 0 ≤ t) (z : ℂ) (u : ℝ) :
    (Real.exp (t * u ^ 2) : ℂ) * Complex.cos (z * u) =
      ∫ v : ℝ, Complex.cos ((z - 2 * Complex.I * Real.sqrt t * v) * u) * (gauss v : ℂ) := by
  set c : ℂ := 2 * Real.sqrt t * u with hc
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr pi_pos).ne'
  have h1 : ∀ v : ℝ, Complex.cos ((z - 2 * Complex.I * Real.sqrt t * v) * u) * (gauss v : ℂ) =
      (1 / (2 * (Real.sqrt π : ℂ))) *
        (Complex.exp (Complex.I * z * u) * Complex.exp (-(v : ℂ) ^ 2 + c * v) +
          Complex.exp (-(Complex.I * z * u)) * Complex.exp (-(v : ℂ) ^ 2 + (-c) * v)) := by
    intro v
    rw [Complex.cos, gauss]
    push_cast
    have e1 : Complex.exp ((z - 2 * Complex.I * Real.sqrt t * v) * u * Complex.I) *
        Complex.exp (-(v : ℂ) ^ 2) =
        Complex.exp (Complex.I * z * u) * Complex.exp (-(v : ℂ) ^ 2 + c * v) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [hc]
      linear_combination (-2 * (Real.sqrt t : ℂ) * u * v) * Complex.I_sq
    have e2 : Complex.exp (-((z - 2 * Complex.I * Real.sqrt t * v) * u) * Complex.I) *
        Complex.exp (-(v : ℂ) ^ 2) =
        Complex.exp (-(Complex.I * z * u)) * Complex.exp (-(v : ℂ) ^ 2 + (-c) * v) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [hc]
      linear_combination (2 * (Real.sqrt t : ℂ) * u * v) * Complex.I_sq
    rw [← e1, ← e2]
    field_simp
  simp_rw [h1]
  rw [integral_const_mul, integral_add ((integrable_cexp_neg_sq_add_mul c).const_mul _)
    ((integrable_cexp_neg_sq_add_mul (-c)).const_mul _), integral_const_mul, integral_const_mul,
    integral_cexp_neg_sq_add_mul, integral_cexp_neg_sq_add_mul]
  have hc2 : c ^ 2 / 4 = t * u ^ 2 := by
    rw [hc]
    have : (Real.sqrt t : ℂ) ^ 2 = t := by exact_mod_cast Real.sq_sqrt ht
    linear_combination this * (u : ℂ) ^ 2
  rw [neg_sq, hc2, Complex.cos, Complex.ofReal_exp]
  push_cast
  field_simp


@[fun_prop]
lemma continuous_phi : Continuous phi := by
  have : phi = fun u => (W'' u - W u) / 8 := funext phi_eq
  rw [this]; fun_prop

lemma norm_phi_le {u : ℝ} (hu : 0 ≤ u) : ‖phi u‖ ≤ C / 4 * g u := by
  rw [phi_eq, norm_div, Real.norm_ofNat]
  have := (norm_sub_le (W'' u) (W u)).trans (add_le_add (norm_W''_le hu) (norm_W_le hu))
  linarith

/-- The `u`-factor of the dominating function in the Fubini argument. -/
lemma integrableOn_norm_phi_mul_exp {t : ℝ} (ht : 0 ≤ t) (b : ℝ) (hb : 0 ≤ b) :
    IntegrableOn (fun u : ℝ => ‖phi u‖ * Real.exp (t * u ^ 2 + b * |u|)) (Ioi 0) := by
  refine integrableOn_Ioi_of_le_exp_neg (by fun_prop) (A := C / 4 * K t b) fun u hu => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hu]
  calc ‖phi u‖ * Real.exp (t * u ^ 2 + b * u) ≤ C / 4 * g u * Real.exp (t * u ^ 2 + b * u) :=
        mul_le_mul_of_nonneg_right (norm_phi_le hu) (Real.exp_pos _).le
    _ = C / 4 * (Real.exp (t * u ^ 2 + b * u) * g u) := by ring
    _ ≤ C / 4 * (K t b * Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left (exp_mul_g_le ht hb hu) (by linarith [C_nonneg])
    _ = _ := by ring

/-- Pointwise domination of the Fubini integrand. -/
lemma norm_integrand_le {t : ℝ} (ht : 0 ≤ t) (z : ℂ) (u v : ℝ) :
    ‖(phi u : ℂ) * (Complex.cos ((z - 2 * Complex.I * Real.sqrt t * v) * u) * (gauss v : ℂ))‖ ≤
      (‖phi u‖ * Real.exp (2 * t * u ^ 2 + |z.im| * |u|)) *
        (Real.exp (-(1 / 2) * v ^ 2) / Real.sqrt π) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs (gauss v),
    abs_of_nonneg (by unfold gauss; positivity)]
  have h1 := norm_cos_mul_le' (z - 2 * Complex.I * Real.sqrt t * v) u
  have him : |(z - 2 * Complex.I * Real.sqrt t * v).im| ≤ |z.im| + 2 * Real.sqrt t * |v| := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    calc _ ≤ |z.im| + |2 * Real.sqrt t * v| := by
          refine (abs_sub _ _).trans_eq' ?_
          congr 1
          ring
      _ = _ := by rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt t)]
  have h2 : Real.exp (|(z - 2 * Complex.I * Real.sqrt t * v).im| * |u|) * (Real.exp (-v ^ 2)) ≤
      Real.exp (2 * t * u ^ 2 + |z.im| * |u|) * Real.exp (-(1 / 2) * v ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h3 := mul_le_mul_of_nonneg_right him (abs_nonneg u)
    have h4 : 0 ≤ (2 * Real.sqrt t * |u| - |v|) ^ 2 := sq_nonneg _
    have h5 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
    have h6 : |u| ^ 2 = u ^ 2 := sq_abs u
    have h7 : |v| ^ 2 = v ^ 2 := sq_abs v
    nlinarith
  unfold gauss
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  calc ‖phi u‖ * (‖Complex.cos ((z - 2 * Complex.I * Real.sqrt t * v) * u)‖ *
        (Real.exp (-v ^ 2) / Real.sqrt π))
      ≤ ‖phi u‖ * (Real.exp (|(z - 2 * Complex.I * Real.sqrt t * v).im| * |u|) *
        (Real.exp (-v ^ 2) / Real.sqrt π)) := by gcongr
    _ = ‖phi u‖ * ((Real.exp (|(z - 2 * Complex.I * Real.sqrt t * v).im| * |u|) *
        Real.exp (-v ^ 2)) / Real.sqrt π) := by ring
    _ ≤ ‖phi u‖ * ((Real.exp (2 * t * u ^ 2 + |z.im| * |u|) * Real.exp (-(1 / 2) * v ^ 2)) /
        Real.sqrt π) := by gcongr
    _ = _ := by ring

/-- **Heat-kernel representation.** For `t ≥ 0`,
`H t z = ∫ H 0 (z - 2 i √t v) e^{-v²}/√π dv`. -/
theorem H_eq_integral_H_zero {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    H t z = ∫ v : ℝ, H 0 (z - 2 * Complex.I * Real.sqrt t * v) * (gauss v : ℂ) := by
  set F : ℝ → ℝ → ℂ := fun u v =>
    (phi u : ℂ) * (Complex.cos ((z - 2 * Complex.I * Real.sqrt t * v) * u) * (gauss v : ℂ)) with hF
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioi 0)).prod volume) := by
    have hA := integrableOn_norm_phi_mul_exp (by linarith : (0:ℝ) ≤ 2 * t) |z.im| (abs_nonneg _)
    have hB : Integrable (fun v : ℝ => Real.exp (-(1 / 2) * v ^ 2) / Real.sqrt π) :=
      (integrable_exp_neg_mul_sq (by norm_num)).div_const _
    refine (hA.mul_prod hB).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Continuous (Function.uncurry F) := by
        rw [hF]; fun_prop
      exact this.aestronglyMeasurable
    · exact norm_integrand_le ht z p.1 p.2
  calc H t z = ∫ u : ℝ in Ioi 0, ∫ v : ℝ, F u v := by
        unfold H
        congr 1
        ext u
        rw [hF]
        simp only
        rw [integral_const_mul, ← exp_mul_cos_eq_integral ht z u]
        push_cast
        ring
    _ = ∫ v : ℝ, ∫ u : ℝ in Ioi 0, F u v := integral_integral_swap hint
    _ = _ := by
        congr 1
        ext v
        unfold H
        rw [← integral_mul_const]
        congr 1
        ext u
        rw [hF]
        simp only [zero_mul, Real.exp_zero, one_mul]
        ring

/-- The heat flow of `ξ`: for `t ≥ 0`,
`H t z = ∫ (1/16 - (1 + (z - 2i√t v)²)/64 · Λ₀((1 + i z)/2 + √t v)) e^{-v²}/√π dv`. -/
theorem H_eq_integral_completedRiemannZeta₀ {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    H t z = ∫ v : ℝ, (1 / 16 - (1 + (z - 2 * Complex.I * Real.sqrt t * v) ^ 2) / 64 *
      completedRiemannZeta₀ ((1 + Complex.I * z) / 2 + Real.sqrt t * v)) * (gauss v : ℂ) := by
  rw [H_eq_integral_H_zero ht]
  congr 1
  ext v
  rw [H_zero_eq, show (1 + Complex.I * (z - 2 * Complex.I * Real.sqrt t * v)) / 2 =
    (1 + Complex.I * z) / 2 + Real.sqrt t * v by
      linear_combination (-(Real.sqrt t : ℂ) * v) * Complex.I_sq]

end DeBruijnNewman
