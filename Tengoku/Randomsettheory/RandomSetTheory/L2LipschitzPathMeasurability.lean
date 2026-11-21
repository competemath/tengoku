/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.ContinuousMapMeasurability
import Tengoku.Randomsettheory.RandomSetTheory.L2LipschitzTruncationResidual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Path-space measurability for Lipschitz empirical processes

The tightness API for Lipschitz empirical processes is formulated for laws on
`C(B, ℝ)`.  This file derives the required path-space measurability from the
already available directional measurability.  Thus applications do not need
to assume separately that the bundled original and truncated processes are
measurable random elements.
-/

open Real Set Finset MeasureTheory Module
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology
open RandomSetTheory

noncomputable section

namespace ProbabilityTheory

variable {Omega Z T iota : Type*} [MeasurableSpace Omega] [MeasurableSpace Z]
  [PseudoMetricSpace T] {mu : Measure Omega}

omit [PseudoMetricSpace T] in
/-- Directional measurability of the original anchored process.-/
theorem measurable_centeredAnchoredEmpiricalProcess
    (H : Z → T → ℝ) (c : ℝ)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t))
    (I : Finset iota) (o t : T) :
    Measurable
      (fun omega ↦ centeredAnchoredEmpiricalProcess
        (mu := mu) H c X I o omega t) := by
  unfold centeredAnchoredEmpiricalProcess
  apply measurable_const.mul
  exact Finset.measurable_fun_sum I fun i _hi ↦
    (measurable_lipschitzIncrement H X hX hH i t o).sub measurable_const

/-- Directional measurability of the anchored truncated process.-/
theorem measurable_centeredAnchoredTruncatedEmpiricalProcess
    (H : Z → T → ℝ) (R : Z → ℝ) (M c : ℝ)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hR : Measurable R)
    (I : Finset iota) (o t : T) :
    Measurable
      (fun omega ↦ centeredAnchoredTruncatedEmpiricalProcess
        (mu := mu) H R M c X I o omega t) := by
  unfold centeredAnchoredTruncatedEmpiricalProcess
  apply measurable_const.mul
  exact Finset.measurable_fun_sum I fun i _hi ↦
    (measurable_truncatedLipschitzIncrement
      H R M X hX hH hR i t o).sub measurable_const

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The bundled original empirical process is a measurable random element of
the continuous path space.-/
theorem measurable_centeredAnchoredEmpiricalContinuousMap
    [IsProbabilityMeasure mu]
    [MeasurableSpace C(EuclideanUnitBall E, ℝ)]
    [BorelSpace C(EuclideanUnitBall E, ℝ)]
    (H : Z → E → ℝ) (R : Z → ℝ)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z))
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (n : ℕ) :
    Measurable
      (centeredAnchoredEmpiricalContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hR hLip hRL2 n) := by
  letI : CompactSpace (EuclideanUnitBall E) :=
    isCompact_iff_compactSpace.mp (by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact isClosed_le continuous_norm continuous_const
      · exact (isBounded_iff_forall_norm_le.mpr
          ⟨1, fun _v hv ↦ hv⟩))
  apply measurable_continuousMap_of_apply
  intro t
  simpa only [centeredAnchoredEmpiricalContinuousMap_apply] using
    (measurable_centeredAnchoredEmpiricalProcess
      (mu := mu) H (Real.sqrt (n + 1 : ℝ))⁻¹ X hX hHmeas
        (Finset.range (n + 1)) 0 (t : E))

/-- The bundled square-root-truncated empirical process is a measurable
random element of the continuous path space.-/
theorem measurable_centeredTruncatedEmpiricalContinuousMap
    [IsProbabilityMeasure mu]
    [MeasurableSpace C(EuclideanUnitBall E, ℝ)]
    [BorelSpace C(EuclideanUnitBall E, ℝ)]
    (H : Z → E → ℝ) (R : Z → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (n : ℕ) :
    Measurable
      (centeredTruncatedEmpiricalContinuousMap (mu := mu)
        H R ha X hX hHmeas hHcont hRmeas hR hLip n) := by
  letI : CompactSpace (EuclideanUnitBall E) :=
    isCompact_iff_compactSpace.mp (by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact isClosed_le continuous_norm continuous_const
      · exact (isBounded_iff_forall_norm_le.mpr
          ⟨1, fun _v hv ↦ hv⟩))
  apply measurable_continuousMap_of_apply
  intro t
  simpa only [centeredTruncatedEmpiricalContinuousMap_apply] using
    (measurable_centeredAnchoredTruncatedEmpiricalProcess
      (mu := mu) H R (a * Real.sqrt (n + 1 : ℝ))
        (Real.sqrt (n + 1 : ℝ))⁻¹ X hX hHmeas hRmeas
        (Finset.range (n + 1)) 0 (t : E))

end Euclidean

end ProbabilityTheory
