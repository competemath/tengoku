/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Tengoku

/-!
# Deformation Volume
-/

@[expose] public section

noncomputable section

namespace EulerDeformationVolume

open Matrix Set MeasureTheory

section ChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A bijective differentiable map with unit Jacobian preserves Lebesgue measure. -/
theorem measurePreserving_of_det_one (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → E) (F : E → E →L[ℝ] E)
    (hf : ∀ x, HasFDerivAt f (F x) x) (hbij : Function.Bijective f)
    (hdet : ∀ x, (F x).det = 1) : MeasurePreserving f μ μ := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  refine ⟨hc.measurable, ?_⟩
  have hm := map_withDensity_abs_det_fderiv_eq_addHaar μ
    (s := (univ : Set E)) (f' := F) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hf x).hasFDerivWithinAt) hbij.1.injOn
  simp only [hdet, abs_one, ENNReal.ofReal_one, Measure.restrict_univ,
    image_univ, hbij.2.range_eq] at hm
  change Measure.map f (μ.withDensity 1) = μ at hm
  rwa [withDensity_one] at hm

end ChangeOfVariables

end EulerDeformationVolume
