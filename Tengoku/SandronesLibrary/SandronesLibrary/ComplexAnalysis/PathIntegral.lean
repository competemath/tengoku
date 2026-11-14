/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.MeasureTheory.Integral.CurveIntegral.Basic
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complex path integrals

This file gives a textbook-facing interface to Mathlib's curve integrals.  A path is Mathlib's
`Path a b`; piecewise-C¹ paths are handled by proving integrability on their C¹ pieces and using
`Path.trans`.  Thus endpoints, reversal, and concatenation are inherited from the topological path
instead of being encoded a second time.

Current entries:

* `complex-analysis.integral.path`: the scalar one-form bridge, path integral, and segment formula;
* `complex-analysis.integral.reparametrization`: reversal, concatenation, and the parameter-space
  change-of-variables formula.
-/

open MeasureTheory
open scoped Interval

noncomputable section

namespace SandronesLibrary.ComplexAnalysis

/-- The complex one-form `f(z) dz`: at `z` it sends a tangent vector `v` to `v * f z`.

> **Entry**: complex-analysis.integral.path-/
def scalarOneForm (f : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z ↦ ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (f z)

/-- Evaluation of the scalar one-form.

> **Entry**: complex-analysis.integral.path-/
@[simp]
theorem scalarOneForm_apply (f : ℂ → ℂ) (z v : ℂ) : scalarOneForm f z v = v * f z := by
  simp [scalarOneForm]

/-- The textbook integral `∫_γ f(z) dz`, implemented by Mathlib's integral of a one-form.

> **Entry**: complex-analysis.integral.path-/
def pathIntegral {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b) : ℂ :=
  ∫ᶜ z in γ, scalarOneForm f z

/-- Integrability of `f(z) dz` along `γ`.

> **Entry**: complex-analysis.integral.path-/
def PathIntegrable {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b) : Prop :=
  CurveIntegrable (scalarOneForm f) γ

/-- Continuity passes from a scalar integrand to its associated one-form.

> **Entry**: complex-analysis.integral.path-/
theorem continuous_scalarOneForm {f : ℂ → ℂ} (hf : Continuous f) :
    Continuous (scalarOneForm f) := by
  exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous.comp hf

/-- A continuous integrand is integrable along a C¹ path.  Piecewise-C¹ paths follow by applying
this theorem to each piece and `PathIntegrable.trans`.

> **Entry**: complex-analysis.integral.path-/
theorem pathIntegrable_of_continuous_of_contDiffOn {a b : ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (hf : Continuous f) (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1)) :
    PathIntegrable f γ := by
  exact (continuous_scalarOneForm hf).continuousOn.curveIntegrable_of_contDiffOn hγ
    (fun _ ↦ Set.mem_univ _)

/-- Reversing a path negates its integral.

> **Entry**: complex-analysis.integral.reparametrization-/
@[simp]
theorem pathIntegral_symm {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b) :
    pathIntegral f γ.symm = -pathIntegral f γ := by
  exact curveIntegral_symm _ _

/-- Reversal preserves path integrability.

> **Entry**: complex-analysis.integral.reparametrization-/
protected theorem PathIntegrable.symm {a b : ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (h : PathIntegrable f γ) : PathIntegrable f γ.symm :=
  CurveIntegrable.symm h

/-- Two integrable paths with a common endpoint have an integrable concatenation.

> **Entry**: complex-analysis.integral.reparametrization-/
protected theorem PathIntegrable.trans {a b c : ℂ} {f : ℂ → ℂ}
    {γ : Path a b} {δ : Path b c} (hγ : PathIntegrable f γ) (hδ : PathIntegrable f δ) :
    PathIntegrable f (γ.trans δ) :=
  CurveIntegrable.trans hγ hδ

/-- The integral along a concatenation is the sum of the two integrals.

> **Entry**: complex-analysis.integral.reparametrization-/
theorem pathIntegral_trans {a b c : ℂ} (f : ℂ → ℂ) (γ : Path a b) (δ : Path b c)
    (hγ : PathIntegrable f γ) (hδ : PathIntegrable f δ) :
    pathIntegral f (γ.trans δ) = pathIntegral f γ + pathIntegral f δ := by
  exact curveIntegral_trans hγ hδ

/-- On a line segment, the path integral has the familiar one-variable formula.

> **Entry**: complex-analysis.integral.path-/
theorem pathIntegral_segment (f : ℂ → ℂ) (a b : ℂ) :
    pathIntegral f (.segment a b) =
      ∫ t in (0 : ℝ)..1, (b - a) * f (AffineMap.lineMap a b t) := by
  rw [pathIntegral, curveIntegral_segment]
  apply intervalIntegral.integral_congr
  intro t _
  simp [scalarOneForm]

/-- The analytic change-of-parameter theorem underlying path reparametrization.  The interval is
oriented, so no monotonicity hypothesis on `φ` is needed.  Taking `g` to be the parameter-space
integrand of a path gives the usual invariance under a C¹ change of parameter.  This is the
parameter-space formula, not yet an equality stated using `Path.reparam`.

> **Entry**: complex-analysis.integral.reparametrization-/
theorem pathIntegral_changeOfVariables {a b : ℝ} (φ φ' : ℝ → ℝ) (g : ℝ → ℂ)
    (hφ : ∀ x ∈ Set.uIcc a b, HasDerivAt φ (φ' x) x)
    (hφ' : ContinuousOn φ' (Set.uIcc a b)) (hg : Continuous g) :
    (∫ x in a..b, φ' x • (g ∘ φ) x) = ∫ u in φ a..φ b, g u := by
  exact intervalIntegral.integral_deriv_smul_comp hφ hφ' hg

end SandronesLibrary.ComplexAnalysis
