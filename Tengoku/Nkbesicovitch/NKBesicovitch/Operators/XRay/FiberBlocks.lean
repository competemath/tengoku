/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Parallel
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.MixedNorm.Fibers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Line families with comparable parallel fibers

Restrict a line family to directions whose fibers have measure in `(a/2,a]`.
The resulting family is Borel, its essential parallel multiplicity is at
most `a`, and every nonzero fiber has measure greater than `a/2`.
No inference from nonemptiness to positive measure is needed.
-/

@[expose] public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m : ℕ}

/-- Restrict a line family to directions with fiber measure in `(a/2,a]`.-/
noncomputable def fiberBlock (F : Set (Line m)) (a : ℝ) : Set (Line m) :=
  F ∩ {g | ENNReal.ofReal (a / 2) < volume ((fun x ↦ (x, g.2)) ⁻¹' F) ∧
    volume ((fun x ↦ (x, g.2)) ⁻¹' F) ≤ ENNReal.ofReal a}

/--
@isnad1 id=le.0h3v.s4.2234cc05bb84 from=translated src=- shape=db5f5255 vocab=0d46a16b
-/
theorem fiberBlock_subset (F : Set (Line m)) (a : ℝ) : fiberBlock F a ⊆ F :=
  inter_subset_left

/--
@isnad1 id=measurab.1h3v.s7.6224906e324b from=translated src=- shape=b3c41b9d vocab=42bf0004
-/
theorem measurableSet_fiberBlock {F : Set (Line m)} (hF : MeasurableSet F) (a : ℝ) :
    MeasurableSet (fiberBlock F a) := by
  have hm : Measurable (fun g : Line m ↦ volume ((fun x ↦ (x, g.2)) ⁻¹' F)) :=
    (measurable_measure_prodMk_right hF).comp measurable_snd
  simpa only [fiberBlock, ofPred_and] using hF.inter
    ((measurableSet_lt (measurable_const (a := ENNReal.ofReal (a / 2))) hm).inter
      (measurableSet_le hm (measurable_const (a := ENNReal.ofReal a))))

/--
@isnad1 id=eq.0h4v.s11.cc133d2472eb from=translated src=- shape=d08fa5ed vocab=894161fc
-/
theorem volume_fiberBlock_fiber (F : Set (Line m)) (a : ℝ)
    (ξ : EuclideanSpace ℝ (Fin m)) :
    volume ((fun x ↦ (x, ξ)) ⁻¹' fiberBlock F a) =
      if ENNReal.ofReal (a / 2) < volume ((fun x ↦ (x, ξ)) ⁻¹' F) ∧
        volume ((fun x ↦ (x, ξ)) ⁻¹' F) ≤ ENNReal.ofReal a
      then volume ((fun x ↦ (x, ξ)) ⁻¹' F) else 0 := by
  classical
  by_cases h : ENNReal.ofReal (a / 2) < volume ((fun x ↦ (x, ξ)) ⁻¹' F) ∧
      volume ((fun x ↦ (x, ξ)) ⁻¹' F) ≤ ENNReal.ofReal a
  · have heq : (fun x ↦ (x, ξ)) ⁻¹' fiberBlock F a = (fun x ↦ (x, ξ)) ⁻¹' F := by
      ext x
      simp [fiberBlock, h]
    simp only [heq, ite_eq_left h]
  · have heq : (fun x ↦ (x, ξ)) ⁻¹' fiberBlock F a = ∅ := by
      ext x
      simp [fiberBlock, h]
    simp only [heq, measure_empty, ite_eq_right h]

/--
@isnad1 id=le.0h4v.s8.58dd001dc17f from=translated src=- shape=1da1ec7d vocab=fb855fc2
-/
theorem volume_fiberBlock_fiber_le (F : Set (Line m)) (a : ℝ)
    (ξ : EuclideanSpace ℝ (Fin m)) :
    volume ((fun x ↦ (x, ξ)) ⁻¹' fiberBlock F a) ≤ ENNReal.ofReal a := by
  rw [volume_fiberBlock_fiber]
  split_ifs with h
  · exact h.2
  · exact zero_le

/--
@isnad1 id=or.0h4v.s9.bba96a45c428 from=translated src=- shape=16fecb1c vocab=01d4c39f
-/
theorem volume_fiberBlock_fiber_gap (F : Set (Line m)) (a : ℝ)
    (ξ : EuclideanSpace ℝ (Fin m)) :
    volume ((fun x ↦ (x, ξ)) ⁻¹' fiberBlock F a) = 0 ∨
      ENNReal.ofReal (a / 2) ≤ volume ((fun x ↦ (x, ξ)) ⁻¹' fiberBlock F a) := by
  rw [volume_fiberBlock_fiber]
  split_ifs with h
  · exact Or.inr h.1.le
  · exact Or.inl rfl

/--
@isnad1 id=le.0h3v.s4.466c49591881 from=translated src=- shape=c09e4d45 vocab=fbdd75b6
-/
theorem parallelMultiplicity_fiberBlock_le (F : Set (Line m)) (a : ℝ) :
    parallelMultiplicity (fiberBlock F a) ≤ ENNReal.ofReal a := by
  exact essSup_le_of_ae_le _ (ae_of_all _ (volume_fiberBlock_fiber_le F a))

/--
@isnad1 id=le.5h5v.s10.abc04d406755 from=translated src=- shape=222ee8c1 vocab=66bc5af4
-/
theorem mixedNorm_fiberBlock_rpow_le {F : Set (Line m)} (hF : MeasurableSet F)
    {q r a : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q / r ≤ 1) (ha : 0 < a) :
    mixedNorm ((fiberBlock F a).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      (ENNReal.ofReal q) (ENNReal.ofReal r) volume volume ^ q ≤
        ENNReal.ofReal ((a / 2) ^ (q / r - 1)) * volume (fiberBlock F a) := by
  rw [Measure.volume_eq_prod]
  exact mixedNorm_indicator_rpow_le_of_fiber_gap (measurableSet_fiberBlock hF a) hq hr hqr
    (by positivity) (fun ξ ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (volume_fiberBlock_fiber_le F a ξ)) (volume_fiberBlock_fiber_gap F a)

end NKBesicovitch.XRay
