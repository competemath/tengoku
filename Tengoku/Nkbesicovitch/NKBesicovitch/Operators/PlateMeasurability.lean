/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Geometry.RigidMotions
public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Topology
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Semicontinuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurability of the plate maximal operator

For every Borel nonnegative input, pull the moving plate indicator back by
the inverse rigid motion. Fatou gives lower semicontinuity on the orthogonal
group, which descends to the Grassmannian through its compact orbit quotient.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

/-- Membership of a fixed point in a rotated open plate is an open condition.-/
theorem isOpen_setOf_mem_plate_rotate (δ : ℝ) (a x : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) :
    IsOpen {u : Rotations n | x ∈ plate δ (Grassmannian.rotate u V).val a} := by
  have heq : {u : Rotations n | x ∈ plate δ (Grassmannian.rotate u V).val a} =
      (fun u : Rotations n ↦ (rigidMotion u a).symm x) ⁻¹' plate δ V.val 0 := by
    ext u
    rw [← preimage_plate_rigidMotion u a V δ]
    simp only [mem_ofPred_eq, mem_preimage, IsometryEquiv.apply_symm_apply]
  rw [heq]
  apply Metric.isOpen_thickening.preimage
  change Continuous (fun u : Rotations n ↦
    ((star u : Rotations n) : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) (x - a))
  exact (continuous_subtype_val.comp continuous_star).clm_apply continuous_const

/-- Fatou's lemma applies to the moving open plate, with the input kept fixed.-/
theorem lowerSemicontinuous_plate_average_orbit (δ : ℝ) (a : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    LowerSemicontinuous (fun u : Rotations n ↦
      (∫⁻ x in plate δ (Grassmannian.rotate u V).val a, f x) /
        volume (plate δ (Grassmannian.rotate u V).val a)) := by
  have hm (u : Rotations n) : MeasurableSet (plate δ (Grassmannian.rotate u V).val a) :=
    Metric.isOpen_thickening.measurableSet
  simp_rw [volume_plate_rotate, div_eq_mul_inv,
    ← lintegral_mul_const _ hf,
    ← lintegral_indicator (hm _)]
  apply lowerSemicontinuous_lintegral
  · intro u
    exact ((hf.mul measurable_const).indicator
      Metric.isOpen_thickening.measurableSet).aemeasurable
  · intro x
    change LowerSemicontinuous
      ({u : Rotations n | x ∈ plate δ (Grassmannian.rotate u V).val a}.indicator
        (fun _ ↦ f x * (volume (plate δ V.val 0))⁻¹))
    exact (isOpen_setOf_mem_plate_rotate δ a x V).lowerSemicontinuous_indicator bot_le

end NKBesicovitch
