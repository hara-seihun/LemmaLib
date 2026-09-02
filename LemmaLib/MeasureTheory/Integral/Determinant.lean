/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integrating determinants coordinatewise

This file moves independent coordinate integrals through a finite determinant. The columnwise and
rowwise forms allow each coordinate to have its own measured space.
-/

open scoped BigOperators

namespace MeasureTheory

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (f : (i j : ι) → X j → 𝕜) (μ : (i : ι) → Measure (X i))

/-- Integrating each column of a matrix separately is the same as integrating its determinant over
the product measure. -/
theorem integral_det_columnwise [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i j, Integrable (f i j) (μ j)) :
    Matrix.det (fun i j ↦ ∫ y, f i j y ∂(μ j)) =
      ∫ x : (j : ι) → X j, Matrix.det (fun i j ↦ f i j (x j)) ∂(Measure.pi μ) := by
  classical
  have hprod (σ : Equiv.Perm ι) :
      Integrable (fun x : (j : ι) → X j ↦ ∏ j, f (σ j) j (x j)) (Measure.pi μ) :=
    Integrable.fintype_prod_dep fun j ↦ hf (σ j) j
  have hterm (σ : Equiv.Perm ι) : Integrable
      (fun x : (j : ι) → X j ↦ ((σ.sign : ℤˣ) : 𝕜) * ∏ j, f (σ j) j (x j))
      (Measure.pi μ) :=
    (hprod σ).const_mul _
  calc
    Matrix.det (fun i j ↦ ∫ y, f i j y ∂(μ j)) =
        ∑ σ : Equiv.Perm ι,
          ((σ.sign : ℤˣ) : 𝕜) * ∏ j, ∫ y, f (σ j) j y ∂(μ j) := by
      simpa using Matrix.det_apply' (fun i j : ι ↦ ∫ y, f i j y ∂(μ j))
    _ = ∑ σ : Equiv.Perm ι, ∫ x : (j : ι) → X j,
          ((σ.sign : ℤˣ) : 𝕜) * ∏ j, f (σ j) j (x j) ∂(Measure.pi μ) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [integral_const_mul, integral_fintype_prod_eq_prod]
    _ = ∫ x : (j : ι) → X j, ∑ σ : Equiv.Perm ι,
          ((σ.sign : ℤˣ) : 𝕜) * ∏ j, f (σ j) j (x j) ∂(Measure.pi μ) := by
      symm
      exact integral_finsetSum Finset.univ fun σ _ ↦ hterm σ
    _ = ∫ x : (j : ι) → X j, Matrix.det (fun i j ↦ f i j (x j)) ∂(Measure.pi μ) := by
      congr 1
      funext x
      exact (Matrix.det_apply' fun i j : ι ↦ f i j (x j)).symm

/-- Integrating each row of a matrix separately is the same as integrating its determinant over the
product measure. -/
theorem integral_det_rowwise [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → ι → X i → 𝕜) (hf : ∀ i j, Integrable (f i j) (μ i)) :
    Matrix.det (fun i j ↦ ∫ y, f i j y ∂(μ i)) =
      ∫ x : (i : ι) → X i, Matrix.det (fun i j ↦ f i j (x i)) ∂(Measure.pi μ) := by
  calc
    Matrix.det (fun i j ↦ ∫ y, f i j y ∂(μ i)) =
        Matrix.det (fun i j ↦ ∫ y, f j i y ∂(μ j)) := by
      exact (Matrix.det_transpose _).symm
    _ = ∫ x : (i : ι) → X i, Matrix.det (fun i j ↦ f j i (x j)) ∂(Measure.pi μ) := by
      exact integral_det_columnwise (fun i j ↦ f j i) μ fun i j ↦ hf j i
    _ = ∫ x : (i : ι) → X i, Matrix.det (fun i j ↦ f i j (x i)) ∂(Measure.pi μ) := by
      congr 1
      funext x
      exact Matrix.det_transpose _

end MeasureTheory
