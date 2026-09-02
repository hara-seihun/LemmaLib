/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Basic

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel

/-!
# Finite differences

This file proves an exact finite Taylor formula for sequences valued in an additive commutative
group.
-/

open scoped BigOperators

private lemma sum_secondDifference {A : Type*} [AddCommGroup A] (f : ℕ → A) (n k : ℕ) :
    ∑ i ∈ Finset.range k,
        ((f (n + i + 2) - f (n + i + 1)) - (f (n + i + 1) - f (n + i))) =
      (f (n + k + 1) - f (n + k)) - (f (n + 1) - f n) := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [Finset.sum_range_succ, hk]
    have harg : n + (k + 2) = n + (k + 1) + 1 := by omega
    rw [← harg]
    abel_nf

/-- An exact finite Taylor formula of order two for an additive-group-valued sequence. -/
theorem sub_sub_nsmul_eq_sum_secondDifference {A : Type*} [AddCommGroup A]
    (f : ℕ → A) (n k : ℕ) :
    f (n + k) - f n - k • (f (n + 1) - f n) =
      ∑ i ∈ Finset.range (k - 1), (k - (i + 1)) •
        ((f (n + i + 2) - f (n + i + 1)) - (f (n + i + 1) - f (n + i))) := by
  cases k with
  | zero => simp
  | succ j =>
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    induction j with
    | zero =>
      simp
      abel
    | succ j hj =>
      rw [Finset.sum_range_succ]
      have hcoef : ∀ i ∈ Finset.range j, j + 1 - i = (j - i) + 1 := by
        intro i hi
        have hi' : i < j := Finset.mem_range.mp hi
        omega
      have hsum := sum_secondDifference f n (j + 1)
      have hrewrite :
          (∑ i ∈ Finset.range j, (j + 1 - i) •
              ((f (n + i + 2) - f (n + i + 1)) - (f (n + i + 1) - f (n + i)))) =
            ∑ i ∈ Finset.range j,
              ((j - i) •
                  ((f (n + i + 2) - f (n + i + 1)) -
                    (f (n + i + 1) - f (n + i))) +
                ((f (n + i + 2) - f (n + i + 1)) -
                  (f (n + i + 1) - f (n + i)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoef i hi, add_nsmul]
        simp only [one_nsmul]
      have hstep :
          f (n + (j + 1 + 1)) - f n - (j + 1 + 1) • (f (n + 1) - f n) =
            (f (n + (j + 1)) - f n - (j + 1) • (f (n + 1) - f n)) +
              ((f (n + j + 2) - f (n + j + 1)) - (f (n + 1) - f n)) := by
        have harg : n + (j + 1 + 1) = n + j + 2 := by omega
        rw [harg]
        simp only [add_nsmul]
        abel_nf
      have hjj : j + 1 - j = 1 := by omega
      rw [hstep, hj, hrewrite, hjj]
      simp only [one_nsmul]
      have hsum' :
          (∑ i ∈ Finset.range (j + 1),
              ((f (n + i + 2) - f (n + i + 1)) - (f (n + i + 1) - f (n + i)))) =
            (f (n + (j + 2)) - f (n + (j + 1))) - (f (n + 1) - f n) := by
        convert hsum using 1; congr 1
      rw [Finset.sum_add_distrib]
      simp only [add_assoc]
      rw [← Finset.sum_range_succ, ← hsum']
      simp only [Nat.add_assoc]
