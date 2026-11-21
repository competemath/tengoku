/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Tengoku.LeanSpectralTheory.Spectral.Cayley.Inverse
import Tengoku.LeanSpectralTheory.Spectral.PVM.Unbounded
import Tengoku.LeanSpectralTheory.Spectral.Spectral.CayleyCalculus
import Tengoku.LeanSpectralTheory.Spectral.Spectral.Polarization
import Tengoku.Seed.Analysis.CStarAlgebra.Spectrum
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Tengoku.Seed.Analysis.InnerProductSpace.StarOrder
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence
import Tengoku.Seed.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Tengoku.Seed.MeasureTheory.Measure.Regular
import Tengoku.Seed.Topology.MetricSpace.HausdorffDistance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spectral theorem: existence

Starting from the continuous functional calculus of the Cayley transform, this file constructs
scalar Riesz measures, polarizes them into operator-valued projections, forms a real PVM by the
inverse Cayley coordinate, and proves that its unbounded coordinate integral is the original
self-adjoint operator.
-/
namespace Tengoku.LeanSpectralTheory end Tengoku.LeanSpectralTheory open Tengoku.LeanSpectralTheory
open MeasureTheory
open CompactlySupported

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private def realToComplexContinuousMap {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) : C(X, ℂ) where
  toFun z := f z
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

@[simp]
private theorem realToComplexContinuousMap_apply {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) (z : X) :
    realToComplexContinuousMap f z = (f z : ℂ) := rfl

@[simp]
private theorem realToComplexContinuousMap_add {X : Type*} [TopologicalSpace X]
    (f g : C_c(X, ℝ)) :
    realToComplexContinuousMap (f + g) =
      realToComplexContinuousMap f + realToComplexContinuousMap g := by
  ext z
  exact Complex.ofReal_add (f z) (g z)

@[simp]
private theorem realToComplexContinuousMap_smul {X : Type*} [TopologicalSpace X]
    (c : ℝ) (f : C_c(X, ℝ)) :
    realToComplexContinuousMap (c • f) =
      (c : ℂ) • realToComplexContinuousMap f := by
  ext z
  exact Complex.ofReal_mul c (f z)

private def compactlySupportedContinuousMap {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℝ)) : C_c(X, ℝ) where
  toFun := f
  hasCompactSupport' := HasCompactSupport.of_compactSpace f

private noncomputable def normalCfcQuadraticLinearMap
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    C_c(spectrum ℂ U, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (@inner ℂ E _ x
    ((cfcHom hU) (realToComplexContinuousMap f) x)).re
  map_add' f g := by
    rw [realToComplexContinuousMap_add, map_add, add_apply,
      inner_add_right, Complex.add_re]
  map_smul' c f := by
    rw [realToComplexContinuousMap_smul, map_smul, smul_apply,
      inner_smul_right, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rfl

private noncomputable def realSqrtContinuousMap {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) : C(X, ℂ) where
  toFun z := Real.sqrt (f z)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp f.continuous)

private noncomputable def continuousMapRealPart {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℂ)) : C_c(X, ℝ) where
  toFun z := (f z).re
  continuous_toFun := Complex.continuous_re.comp f.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

private noncomputable def continuousMapImagPart {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℂ)) : C_c(X, ℝ) where
  toFun z := (f z).im
  continuous_toFun := Complex.continuous_im.comp f.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

private noncomputable def continuousMapOfRealPart {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) : C(X, ℂ) where
  toFun z := ((f z).re : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp f.continuous)

private noncomputable def continuousMapOfImagPart {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) : C(X, ℂ) where
  toFun z := ((f z).im : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Complex.continuous_im.comp f.continuous)

private noncomputable def normalCfcRealOperator
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f : C(spectrum ℂ U, ℝ)) : E →L[ℂ] E :=
  (cfcHom hU) (realToComplexContinuousMap (compactlySupportedContinuousMap f))

private noncomputable def closedSetApprox
    {X : Type*} [PseudoMetricSpace X] (K : Set X) (n : ℕ) : C(X, ℝ) where
  toFun z := max 0 (1 - (n : ℝ) * Metric.infDist z K)
  continuous_toFun := continuous_const.max
    (continuous_const.sub (continuous_const.mul (Metric.continuous_infDist_pt K)))

private def compactlySupportedOne (X : Type*) [TopologicalSpace X]
    [CompactSpace X] : C_c(X, ℝ) where
  toFun := 1
  hasCompactSupport' := HasCompactSupport.of_compactSpace 1

@[simp]
private theorem compactlySupportedOne_apply (X : Type*) [TopologicalSpace X]
    [CompactSpace X] (z : X) : compactlySupportedOne X z = 1 := rfl

private def initialUnion {X : Type*} (S : ℕ → Set X) (n : ℕ) : Set X :=
  ⋃ i, ⋃ (_hi : i < n), S i

private def tailUnion {X : Type*} (S : ℕ → Set X) (n : ℕ) : Set X :=
  ⋃ i, ⋃ (_hi : n ≤ i), S i

private def unitPole (U : E →L[ℂ] E) : Set (spectrum ℂ U) :=
  {z | (z : ℂ) = 1}

private noncomputable def distanceToOneSq (U : E →L[ℂ] E) :
    C_c(spectrum ℂ U, ℝ) where
  toFun z := ‖(z : ℂ) - 1‖ ^ 2
  continuous_toFun := ((continuous_subtype_val.sub continuous_const).norm.pow 2)
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

private noncomputable def distanceToOneSqComplex (U : E →L[ℂ] E) :
    C(spectrum ℂ U, ℂ) :=
  star ((ContinuousMap.id ℂ).restrict (spectrum ℂ U) - 1) *
    ((ContinuousMap.id ℂ).restrict (spectrum ℂ U) - 1)

/-- The real inverse-Cayley coordinate, with the removable spectral point `1` assigned `0` by
the field convention `0⁻¹ = 0`.-/
noncomputable def _root_.Tengoku.LeanSpectralTheory.inverseCayleyCoordinate (z : ℂ) : ℝ :=
  -z.im / (1 - z.re)

/-- The scalar Cayley coordinate on the real line.-/
noncomputable def _root_.Tengoku.LeanSpectralTheory.cayleyCoordinate (t : ℝ) : ℂ :=
  ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)
-- Tengoku: root names of this library moved to Tengoku.LeanSpectralTheory so they do not collide with other libraries (generated)
