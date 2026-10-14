/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.Grunbaum.ProbabilityCore
public import Tengoku.LeanPool.LeanPool.Feige.Grunbaum.TruncationConcavity
import Tengoku.LeanPool.LeanPool.Feige.Grunbaum.FinalBridge
public import Tengoku

/-!
# Grünbaum's centroid halfspace theorem

This file closes the geometric, measure-theoretic, and Jensen layers of the
proof.  The public theorem `grunbaum_centroid_halfspace` has only the
assumptions in the mathematical statement.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace Grunbaum

/--
@isnad1 id=eq.2h4v.s10.c2ba35dc4bf9 from=translated src=- shape=e8b7515f vocab=26933dbc
-/
lemma truncDomain_eq_Ici_of_isMinOn {d : ℕ} {C : Set (Euc d)}
    {ℓ : Euc d →L[ℝ] ℝ} {x₀ : Euc d}
    (hx₀ : x₀ ∈ C) (hmin : IsMinOn ℓ C x₀) :
    truncDomain C ℓ = Ici (ℓ x₀) := by
  ext t
  constructor
  · intro ht
    change (trunc C ℓ t).Nonempty at ht
    obtain ⟨x, hxC, hxℓ⟩ := ht
    change ℓ x ≤ t at hxℓ
    exact (hmin hxC).trans hxℓ
  · intro ht
    change (trunc C ℓ t).Nonempty
    exact ⟨x₀, hx₀, ht⟩

/--
@isnad1 id=eq.0h4v.s12.bc1ed18a80fc from=translated src=- shape=da1e4c37 vocab=167d70fe
-/
lemma cdf_map_uniformVolume_eq_truncVolumeRatio {d : ℕ}
    (C : Set (Euc d)) (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ)
    [IsProbabilityMeasure ((uniformVolume C).map ℓ)] :
    cdf ((uniformVolume C).map ℓ) t =
      (volume (trunc C ℓ t) / volume C).toReal := by
  rw [cdf_eq_real, measureReal_def,
    Measure.map_apply ℓ.measurable measurableSet_Iic]
  have hm : MeasurableSet (ℓ ⁻¹' Iic t) :=
    measurableSet_Iic.preimage ℓ.measurable
  simp only [uniformVolume, Measure.smul_apply,
    Measure.restrict_apply hm, smul_eq_mul, trunc, div_eq_mul_inv]
  rw [inter_comm, mul_comm]

/--
@isnad1 id=eq.0h4v.s11.6fad40a7110e from=translated src=- shape=3fc100dd vocab=251d1f9f
-/
lemma cdfRoot_eq_cdf_rpow_map_uniformVolume {d : ℕ}
    (C : Set (Euc d)) (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ)
    [IsProbabilityMeasure ((uniformVolume C).map ℓ)] :
    cdfRoot C ℓ t =
      cdf ((uniformVolume C).map ℓ) t ^
        ((((d + 1 : ℕ) : ℝ))⁻¹) := by
  rw [cdf_map_uniformVolume_eq_truncVolumeRatio]
  unfold cdfRoot
  rw [ENNReal.toReal_rpow]
  simp only [Nat.cast_add, Nat.cast_one]

/--
@isnad1 id=eventual.1h4v.s11.1683053b1fa3 from=translated src=- shape=e9c59bbf vocab=77a22ec5
-/
lemma ae_map_uniformVolume_mem_Ici_of_isMinOn {d : ℕ}
    (C : FullDimensionalConvexBody d) (ℓ : Euc d →L[ℝ] ℝ)
    {x₀ : Euc d} (hmin : IsMinOn ℓ (C : Set (Euc d)) x₀) :
    ∀ᵐ t ∂(uniformVolume (C : Set (Euc d))).map ℓ, t ∈ Ici (ℓ x₀) := by
  change ∀ᵐ t ∂(uniformVolume (C : Set (Euc d))).map ℓ, ℓ x₀ ≤ t
  rw [ae_map_iff ℓ.measurable.aemeasurable measurableSet_Ici]
  unfold uniformVolume
  apply Measure.ae_smul_measure
  rw [ae_iff]
  have hm : MeasurableSet {x : Euc d | ¬ℓ x₀ ≤ ℓ x} := by
    simpa only [not_le] using
      (measurableSet_lt ℓ.measurable measurable_const)
  rw [Measure.restrict_apply hm]
  have hempty :
      {x : Euc d | ¬ℓ x₀ ≤ ℓ x} ∩ (C : Set (Euc d)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (hmin hx.2)
  rw [hempty, measure_empty]

/--
@isnad1 id=integrab.0h3v.s10.490ec6f08a17 from=translated src=- shape=f9375695 vocab=ac330fb9
-/
lemma integrable_id_map_uniformVolume {d : ℕ}
    (C : FullDimensionalConvexBody d) (ℓ : Euc d →L[ℝ] ℝ) :
    Integrable (fun t : ℝ ↦ t)
      ((uniformVolume (C : Set (Euc d))).map ℓ) := by
  have hid_restrict :
      Integrable (fun x : Euc d ↦ x)
        (volume.restrict (C : Set (Euc d))) :=
    continuous_id.continuousOn.integrableOn_compact C.isCompact
  have hid_uniform :
      Integrable (fun x : Euc d ↦ x)
        (uniformVolume (C : Set (Euc d))) := by
    simpa [uniformVolume, Measure.restrict_apply_univ] using
      hid_restrict.to_average
  apply (integrable_map_measure continuous_id.aestronglyMeasurable
    ℓ.measurable.aemeasurable).2
  simpa [Function.comp_def] using ℓ.integrable_comp hid_uniform

end Grunbaum
