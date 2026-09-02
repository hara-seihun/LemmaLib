/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Subsequences in pseudometric spaces

This file gives a diagonal construction of a separated subsequence from eventual pointwise
separation.
-/

open Filter

/-- If every fixed term of a sequence is eventually at distance at least `r` from its tail, then the
sequence has a strictly increasing `r`-separated subsequence. -/
theorem exists_strictMono_dist_ge {X : Type*} [PseudoMetricSpace X] (x : ℕ → X) (r : ℝ)
    (h : ∀ i, ∀ᶠ j in atTop, r ≤ dist (x j) (x i)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k l, k < l → r ≤ dist (x (s l)) (x (s k)) := by
  have htail : ∀ i, ∃ N, ∀ j, N ≤ j → r ≤ dist (x j) (x i) :=
    fun i ↦ eventually_atTop.mp (h i)
  choose N hN using htail
  let s : ℕ → ℕ := Nat.rec 0 fun _ previous ↦
    max (previous + 1) (∑ i ∈ Finset.range (previous + 1), N i)
  have hs_succ (n : ℕ) :
      s (n + 1) = max (s n + 1) (∑ i ∈ Finset.range (s n + 1), N i) := by
    simp [s]
  have hthreshold (n : ℕ) : N (s n) ≤ s (n + 1) := by
    rw [hs_succ]
    apply le_trans _ (le_max_right _ _)
    apply Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    simp
  have hs_step (n : ℕ) : s n < s (n + 1) := by
    rw [hs_succ]
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hs : StrictMono s := strictMono_nat_of_lt_succ hs_step
  refine ⟨s, hs, ?_⟩
  intro k l hkl
  apply hN (s k) (s l)
  exact (hthreshold k).trans (hs.monotone (Nat.succ_le_iff.mpr hkl))
