/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Isolating a zero by its derivative

A continuous real function whose endpoint values have opposite signs has an interior zero. If its
derivative never vanishes on the interval, that zero is unique.
-/

open Set

/-- A continuous real function whose values at the endpoints have opposite signs has a zero in the
open interval. -/
theorem exists_eq_zero_mem_Ioo_of_mul_neg {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hneg : f a * f b < 0) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  have hzero : (0 : ℝ) ∈ Icc (f a) (f b) ∨ (0 : ℝ) ∈ Icc (f b) (f a) := by
    rcases mul_neg_iff.mp hneg with h | h
    · exact Or.inr ⟨h.2.le, h.1.le⟩
    · exact Or.inl ⟨h.1.le, h.2.le⟩
  obtain ⟨x, hx, hfx⟩ : ∃ x ∈ Icc a b, f x = 0 := by
    rcases hzero with hzero | hzero
    · exact intermediate_value_Icc hab.le hf hzero
    · exact intermediate_value_Icc' hab.le hf hzero
  have hfa : f a ≠ 0 := fun ha ↦ by simpa [ha] using hneg.ne
  have hfb : f b ≠ 0 := fun hb ↦ by simpa [hb] using hneg.ne
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hfx⟩
  · rintro rfl
    exact hfa hfx
  · rintro rfl
    exact hfb hfx

/-- Two zeros in an interval coincide if the derivative never vanishes between them. -/
theorem eq_of_mem_Icc_of_eq_zero_of_deriv_ne_zero {f : ℝ → ℝ} {a b x y : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ z ∈ Ioo a b, deriv f z ≠ 0) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hfx : f x = 0) (hfy : f y = 0) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · obtain ⟨z, hz, hz'⟩ := exists_deriv_eq_slope f hxy
      (hf.mono fun _ hz ↦ ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩)
      (hf'.mono fun _ hz ↦ ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩)
    exact False.elim <| hderiv z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩ <| by
      rw [hz', hfx, hfy, sub_self, zero_div]
  · exact hxy
  · obtain ⟨z, hz, hz'⟩ := exists_deriv_eq_slope f hxy
      (hf.mono fun _ hz ↦ ⟨hy.1.trans hz.1, hz.2.trans hx.2⟩)
      (hf'.mono fun _ hz ↦ ⟨hy.1.trans_lt hz.1, hz.2.trans_le hx.2⟩)
    exact False.elim <| hderiv z ⟨hy.1.trans_lt hz.1, hz.2.trans_le hx.2⟩ <| by
      rw [hz', hfy, hfx, sub_self, zero_div]

/-- A continuous real function with opposite signs at the endpoints and nonvanishing derivative in
between has a unique zero in the open interval. -/
theorem existsUnique_eq_zero_mem_Ioo_of_deriv_ne_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hf' : DifferentiableOn ℝ f (Ioo a b))
    (hneg : f a * f b < 0) (hderiv : ∀ x ∈ Ioo a b, deriv f x ≠ 0) :
    ∃! x, x ∈ Ioo a b ∧ f x = 0 := by
  obtain ⟨x, hx, hfx⟩ := exists_eq_zero_mem_Ioo_of_mul_neg hab hf hneg
  refine ⟨x, ⟨hx, hfx⟩, fun y hy ↦ ?_⟩
  exact eq_of_mem_Icc_of_eq_zero_of_deriv_ne_zero (x := y) (y := x) hf hf' hderiv
    ⟨hy.1.1.le, hy.1.2.le⟩ ⟨hx.1.le, hx.2.le⟩ hy.2 hfx
