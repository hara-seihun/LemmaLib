import Mathlib
open Finset
example (f : ℕ → ℂ) (N : ℕ) : ∑ n ∈ Icc 1 N, f n = ∑ n ∈ range N, f (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]
example {f : ℝ → ℂ} (hf : MeasureTheory.Integrable f) : MeasureTheory.Integrable fun v => (starRingEnd ℂ) (f v) :=
  hf.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hf.1) (MeasureTheory.ae_of_all _ fun v => by simp)
example (f : ℝ → ℂ) : ∫ v, f (-v) = ∫ v, f v := MeasureTheory.integral_neg_eq_self f _
example {f : ℝ → ℂ} (hf : MeasureTheory.Integrable f) : MeasureTheory.Integrable fun v => f (-v) := hf.comp_neg
