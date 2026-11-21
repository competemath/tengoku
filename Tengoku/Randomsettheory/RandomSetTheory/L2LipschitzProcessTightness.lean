/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.L2LipschitzEuclideanChaining
import Tengoku.Randomsettheory.RandomSetTheory.ProcessTightnessCriterion
import Tengoku.Seed.Topology.ContinuousMap.SecondCountableSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tightness of a truncated `L²` Lipschitz empirical process

This file combines the dyadic oscillation estimates with Arzelà--Ascoli.
The output is genuine tightness of the pushforward laws on the continuous
path space over a finite-dimensional Euclidean unit ball.
-/

open Filter Real Set Finset MeasureTheory Module
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology
open RandomSetTheory

noncomputable section

namespace ProbabilityTheory

variable {Omega Z E : Type*} [MeasurableSpace Omega] [MeasurableSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {mu : Measure Omega}

/-- The centered truncated empirical process bundled as a continuous path on
the Euclidean unit ball.-/
def centeredTruncatedEmpiricalContinuousMap
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (n : ℕ) (omega : Omega) : C(EuclideanUnitBall E, ℝ) where
  toFun t := centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
    (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
    (Finset.range (n + 1)) 0 omega (t : E)
  continuous_toFun :=
    (continuous_centeredAnchoredTruncatedEmpiricalProcess
      H R (mul_nonneg ha (Real.sqrt_nonneg _)) X hX hHmeas hHcont
        hRmeas hR hLip (Finset.range (n + 1)) 0 omega).comp
          continuous_subtype_val

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/--
@isnad1 id=eq.7h11v.s8.1c913b01d581 from=translated src=- shape=2bb361df vocab=a2e66082
-/
@[simp]
theorem centeredTruncatedEmpiricalContinuousMap_apply
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (n : ℕ) (omega : Omega) (t : EuclideanUnitBall E) :
    centeredTruncatedEmpiricalContinuousMap (mu := mu)
        H R ha X hX hHmeas hHcont hRmeas hR hLip n omega t =
      centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
        (a * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
        (Finset.range (n + 1)) 0 omega (t : E) := rfl

omit [CompleteSpace E] in
/-- Uniform tightness of all sample-size laws of the centered, truncated
empirical process.  Measurability of the bundled path is kept explicit; in
random-set applications it is supplied by the measurable support-map layer.
@isnad1 id=istightm.12h9v.s9.f823f489c70e from=translated src=- shape=25eea7ee vocab=30089aa0
-/
theorem isTightMeasureSet_range_centeredTruncatedEmpiricalContinuousMap
    [IsProbabilityMeasure mu]
    [MeasurableSpace C(EuclideanUnitBall E, ℝ)]
    [BorelSpace C(EuclideanUnitBall E, ℝ)]
    (H : Z → E → ℝ) (R : Z → ℝ) {a K : ℝ}
    (ha : 0 ≤ a) (hK : 0 < K)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (hpathMeas : ∀ n, AEMeasurable
      (centeredTruncatedEmpiricalContinuousMap (mu := mu)
        H R ha X hX hHmeas hHcont hRmeas hR hLip n) mu) :
    IsTightMeasureSet (Set.range fun n ↦ mu.map
      (centeredTruncatedEmpiricalContinuousMap (mu := mu)
        H R ha X hX hHmeas hHcont hRmeas hR hLip n)) := by
  letI : CompactSpace (EuclideanUnitBall E) :=
    isCompact_iff_compactSpace.mp (by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact isClosed_le continuous_norm continuous_const
      · exact (isBounded_iff_forall_norm_le.mpr
          ⟨1, fun _v hv ↦ hv⟩))
  let d := finrank ℝ E
  let Y : ℕ → Omega → C(EuclideanUnitBall E, ℝ) := fun n ↦
    centeredTruncatedEmpiricalContinuousMap (mu := mu)
      H R ha X hX hHmeas hHcont hRmeas hR hLip n
  let delta : ℕ → ℝ := RandomSetTheory.dyadicResolution
  apply isTightMeasureSet_range_map_of_real_norm_and_modulus
    mu Y hpathMeas delta RandomSetTheory.dyadicResolution_pos
  intro epsilon hepsilon
  have hevent : ∀ᶠ x : ℝ in atTop, Real.exp (-x) < epsilon / 2 :=
    tendsto_exp_neg_atTop_nhds_zero (Iio_mem_nhds (half_pos hepsilon))
  obtain ⟨x, hxTail, hx⟩ :=
    (hevent.and (eventually_ge_atTop (0 : ℝ))).exists
  let B := mixedEuclideanProcessBound (2 * K) (2 * a) d x
  let eta : ℕ → ℝ := fun k ↦
    2 * mixedEuclideanProcessBound
      (2 * ((2 * delta k) * K)) (2 * ((2 * delta k) * a)) d
        (mixedEuclideanConfidence d x k)
  let p : ℕ → ℝ := mixedEuclideanEntropyCost d x
  refine ⟨B, mixedEuclideanProcessBound_nonneg (by positivity)
      (by positivity) d hx, eta, ?_, p, ?_, ?_, ?_, ?_, ?_⟩
  · have hs := summable_dyadic_mixedEuclideanProcessBound
      (4 * K) (4 * a) d hx
    have hs2 := hs.mul_left (2 : ℝ)
    have hetaSummable : Summable eta := by
      apply hs2.congr
      intro k
      dsimp only [eta, delta, RandomSetTheory.dyadicResolution]
      congr 2 <;> ring
    exact hetaSummable.tendsto_atTop_zero
  · intro k
    unfold p mixedEuclideanEntropyCost
    positivity
  · exact summable_mixedEuclideanEntropyCost d x
  · exact (tsum_mixedEuclideanEntropyCost_le d x).trans hxTail.le
  · intro n
    have hglobal :=
      measureReal_unitBall_range_succ_centeredTruncated_largeDeviation_le
        H R ha hK hx X hX hIndep hHmeas hHcont hRmeas hR hLip
          hRL2 hRsecond n
    refine ((measureReal_mono ?_).trans hglobal).trans hxTail.le
    intro omega homega
    have hnotall : ¬ ∀ t : EuclideanUnitBall E,
        |Y n omega t| ≤ B := by
      intro hall
      exact (not_le_of_gt homega)
        (ContinuousMap.norm_le (Y n omega)
          (mixedEuclideanProcessBound_nonneg (by positivity)
            (by positivity) d hx) |>.2 (fun t ↦ by
              simpa only [Real.norm_eq_abs] using hall t))
    push Not at hnotall
    obtain ⟨t, ht⟩ := hnotall
    refine ⟨t, ?_⟩
    simpa only [Y, B, centeredTruncatedEmpiricalContinuousMap_apply] using ht
  · intro n k
    have hosc :=
      measureReal_unitBall_dyadicOscillation_range_succ_centeredTruncated_le
        H R ha hK hx X hX hIndep hHmeas hHcont hRmeas hR hLip
          hRL2 hRsecond n k
    simpa only [Y, delta, eta, p, Real.dist_eq,
      centeredTruncatedEmpiricalContinuousMap_apply] using hosc

end ProbabilityTheory
