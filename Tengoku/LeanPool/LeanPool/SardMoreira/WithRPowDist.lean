/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.SardMoreira.ToMathlib.PR33114

/-!
# LeanPool.SardMoreira.WithRPowDist
-/

@[expose] public section

open scoped ENNReal NNReal Filter Uniformity Topology
open Function

noncomputable section

namespace WithRPowDist

variable {X : Type*} {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1}

variable [MeasurableSpace X]

instance : MeasurableSpace (WithRPowDist X α hα₀ hα₁) := .comap WithRPowDist.val ‹_›

@[fun_prop]
theorem measurable_val : Measurable (val : WithRPowDist X α hα₀ hα₁ → X) :=
  comap_measurable _

@[fun_prop]
theorem measurable_mk : Measurable (mk : X → WithRPowDist X α hα₀ hα₁) :=
  .of_comap_le <| by
    rw [instMeasurableSpace, MeasurableSpace.comap_comp, val_comp_mk, MeasurableSpace.comap_id]

/-- The natural measurable equivalence between `WithRPowDist X α hα₀ hα₁` and `X`. -/
@[simps! -fullyApplied toEquiv apply symm_apply]
def measurableEquiv : WithRPowDist X α hα₀ hα₁ ≃ᵐ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁
  measurable_toFun := measurable_val
  measurable_invFun := measurable_mk

theorem measurableEmbedding_mk : MeasurableEmbedding (mk : X → WithRPowDist X α hα₀ hα₁) :=
  measurableEquiv.symm.measurableEmbedding

instance [TopologicalSpace X] [BorelSpace X] : BorelSpace (WithRPowDist X α hα₀ hα₁) :=
  measurableEquiv.measurableEmbedding.borelSpace homeomorph.isInducing

end WithRPowDist

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1} {μ : Measure X}

open WithRPowDist

variable (α hα₀ hα₁) in
/-- The pushforward of a measure `μ` on `X` under the canonical map
`X → WithRPowDist X α hα₀ hα₁`. -/
def withRPowDist (μ : Measure X) : Measure (WithRPowDist X α hα₀ hα₁) :=
  μ.map .mk

theorem withRPowDist_apply (μ : Measure X) (s : Set (WithRPowDist X α hα₀ hα₁)) :
    μ.withRPowDist α hα₀ hα₁ s = μ (.mk ⁻¹' s) := by
  rw [withRPowDist, measurableEmbedding_mk.map_apply]

instance [TopologicalSpace X] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.withRPowDist α hα₀ hα₁) where
  finiteAtNhds := by
    rintro ⟨x⟩
    rcases μ.finiteAt_nhds x with ⟨s, hsx, hμs⟩
    simp only [homeomorph.nhds_eq_comap, homeomorph_apply]
    refine ⟨_, Filter.preimage_mem_comap hsx, ?_⟩
    rwa [withRPowDist, measurableEmbedding_mk.map_apply]

@[simp]
theorem withRPowDist_hausdorffMeasure [EMetricSpace X] [BorelSpace X] (d : ℝ) :
    (μH[d] : Measure X).withRPowDist α hα₀ hα₁ = μH[d / α] := by
  ext s hs
  simp only [withRPowDist_apply, hausdorffMeasure_apply,
    ← (Surjective.piMap fun _ : ℕ ↦ (@injective_mk X α hα₀ hα₁).preimage_surjective).iInf_comp,
    Pi.map_apply, ← Set.preimage_iUnion, surjective_mk.preimage_subset_preimage_iff,
    ediam_preimage_mk, surjective_mk.nonempty_preimage, ENNReal.rpow_inv_le_iff hα₀]
  apply (ENNReal.rpow_left_surjective hα₀.ne').iSup_congr
  intro r
  simp [← ENNReal.rpow_mul, div_eq_inv_mul, pos_iff_ne_zero, hα₀, hα₀.le]

instance [PseudoMetricSpace X] [IsUnifLocDoublingMeasure μ] :
    IsUnifLocDoublingMeasure (μ.withRPowDist α hα₀ hα₁) where
  exists_measure_closedBall_le_mul'' := by
    use IsUnifLocDoublingMeasure.scalingConstantOf μ (2 ^ α⁻¹)
    rcases (nhdsGT_basis _).eventually_iff.mp
      (IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul μ (2 ^ α⁻¹))
      with ⟨r, hr₀, hr⟩
    filter_upwards [Ioo_mem_nhdsGT (show 0 < r ^ α by positivity)]
    rintro a ⟨ha₀, ha⟩ ⟨x⟩
    simpa (disch := positivity) [withRPowDist_apply, Real.mul_rpow, Real.rpow_pos_of_pos,
      Real.rpow_inv_lt_iff_of_pos, *] using fun h ↦ @hr (a ^ α⁻¹) h x

end MeasureTheory.Measure
