/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted Cesàro estimates

This file proves that triangular Cesàro weighting preserves a little-o estimate for sequences
converging to zero.
-/

open Filter Finset
open scoped Topology

namespace Asymptotics

/-- A real sequence converging to zero remains negligible compared with `n ^ 2` after triangular
Cesàro weighting. -/
theorem isLittleO_weighted_sum_range_of_tendsto_zero (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    (fun n : ℕ ↦ ∑ j ∈ range n, ((n : ℝ) - (j + 1 : ℕ)) * ε (j + 1))
      =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  have hshift : Tendsto (fun j : ℕ ↦ ε (j + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hε
  have hpartial :
      (fun n : ℕ ↦ ∑ j ∈ range n, ε (j + 1)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
    isLittleO_sum_range_of_tendsto_zero hshift
  have hfirst :
      (fun n : ℕ ↦ (n : ℝ) * ∑ j ∈ range n, ε (j + 1))
        =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
    simpa only [pow_two] using
      (isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop).mul_isLittleO hpartial
  have hterm :
      (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * ε (j + 1))
        =o[atTop] (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ)) := by
    have he : (fun j : ℕ ↦ ε (j + 1)) =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) :=
      (isLittleO_one_iff ℝ).2 hshift
    simpa only [mul_one] using
      (isBigO_refl (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ)) atTop).mul_isLittleO he
  have hweights_tendsto :
      Tendsto (fun n : ℕ ↦ ∑ j ∈ range n, ((j + 1 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n ↦ ?_) tendsto_natCast_atTop_atTop
    calc
      (n : ℝ) = ∑ _j ∈ range n, (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ range n, ((j + 1 : ℕ) : ℝ) := by
        exact sum_le_sum fun j _ ↦ by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hsecond_raw :
      (fun n : ℕ ↦ ∑ j ∈ range n, ((j + 1 : ℕ) : ℝ) * ε (j + 1))
        =o[atTop] (fun n : ℕ ↦ ∑ j ∈ range n, ((j + 1 : ℕ) : ℝ)) :=
    hterm.sum_range (fun _ ↦ by positivity) hweights_tendsto
  have hweights_bigO :
      (fun n : ℕ ↦ ∑ j ∈ range n, ((j + 1 : ℕ) : ℝ))
        =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
    apply isBigO_iff.2
    refine ⟨1, Filter.Eventually.of_forall fun n ↦ ?_⟩
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity),
      Real.norm_of_nonneg (sq_nonneg (n : ℝ)), one_mul]
    calc
      ∑ j ∈ range n, ((j + 1 : ℕ) : ℝ) ≤ ∑ _j ∈ range n, (n : ℝ) := by
        exact sum_le_sum fun j hj ↦ by
          exact_mod_cast Nat.succ_le_iff.mpr (mem_range.mp hj)
      _ = (n : ℝ) * (n : ℝ) := by simp
      _ = (n : ℝ) ^ 2 := by ring
  have hsecond :
      (fun n : ℕ ↦ ∑ j ∈ range n, ((j + 1 : ℕ) : ℝ) * ε (j + 1))
        =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) :=
    hsecond_raw.trans_isBigO hweights_bigO
  refine (hfirst.sub hsecond).congr_left ?_
  intro n
  simp_rw [sub_mul]
  rw [sum_sub_distrib, ← mul_sum]

end Asymptotics
