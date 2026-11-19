/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Action
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rigid motions of disks and plates

Translations and orthogonal operators preserve Lebesgue volume and carry the
disk and plate in a fixed direction to the corresponding rotated direction.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch

variable {n k : ℕ}

/-- Apply an orthogonal operator and then translate the center to `a`.-/
noncomputable def rigidMotion (u : Rotations n) (a : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ᵢ EuclideanSpace ℝ (Fin n) :=
  (Unitary.linearIsometryEquiv u).toIsometryEquiv.trans (IsometryEquiv.vaddConst a)

/--
@isnad1 id=eq.0h4v.s15.c25ec9aeece4 from=translated src=- shape=a48f67ac vocab=bd7e4c40
-/
theorem rigidMotion_apply (u : Rotations n) (a x : EuclideanSpace ℝ (Fin n)) :
    rigidMotion u a x = Unitary.linearIsometryEquiv u x + a := rfl

/--
@isnad1 id=measurep.0h3v.s12.5cb2daf54746 from=translated src=- shape=1e51fe96 vocab=1af751d2
-/
theorem measurePreserving_rigidMotion (u : Rotations n) (a : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (rigidMotion u a) volume volume :=
  (Unitary.linearIsometryEquiv u).measurePreserving.add_right volume a

/--
@isnad1 id=eq.0h5v.s12.a476e003ab55 from=translated src=- shape=b71c4139 vocab=983d33fe
-/
theorem preimage_unitDisk_rigidMotion (u : Rotations n) (a : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) :
    rigidMotion u a ⁻¹' unitDisk (Grassmannian.rotate u V).val a =
      unitDisk V.val 0 := by
  ext x
  simp only [Set.mem_preimage, unitDisk, Set.mem_ofPred_eq, rigidMotion_apply,
    add_sub_cancel_right, sub_zero, LinearIsometryEquiv.norm_map]
  apply and_congr_left
  intro _
  change Unitary.linearIsometryEquiv u x ∈
    Unitary.linearIsometryEquiv u '' (V.val : Set (EuclideanSpace ℝ (Fin n))) ↔
      x ∈ (V.val : Set (EuclideanSpace ℝ (Fin n)))
  simp only [Set.mem_image, (Unitary.linearIsometryEquiv u).injective.eq_iff, exists_eq_right]

/--
@isnad1 id=eq.0h5v.s12.304d0f61b12f from=translated src=- shape=5897ee9a vocab=fb499337
-/
theorem image_unitDisk_rigidMotion (u : Rotations n) (a : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) :
    rigidMotion u a '' unitDisk V.val 0 =
      unitDisk (Grassmannian.rotate u V).val a := by
  rw [← preimage_unitDisk_rigidMotion u a V]
  exact (rigidMotion u a).surjective.image_preimage _

/--
@isnad1 id=eq.0h6v.s12.c3f2ae898cbf from=translated src=- shape=4d72c50d vocab=399acdd9
-/
theorem preimage_plate_rigidMotion (u : Rotations n) (a : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) (δ : ℝ) :
    rigidMotion u a ⁻¹' plate δ (Grassmannian.rotate u V).val a =
      plate δ V.val 0 := by
  rw [plate, ← image_unitDisk_rigidMotion u a V]
  ext x
  simp only [Set.mem_preimage, plate, Metric.mem_thickening_iff_infEDist_lt,
    Metric.infEDist_image (rigidMotion u a).isometry]

/--
@isnad1 id=eq.0h6v.s12.33361fa4f5c7 from=translated src=- shape=471a5f20 vocab=a137e9a1
-/
theorem volume_plate_rotate (u : Rotations n) (a : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) (δ : ℝ) :
    volume (plate δ (Grassmannian.rotate u V).val a) =
      volume (plate δ V.val 0) := by
  rw [← preimage_plate_rigidMotion u a V δ]
  exact ((measurePreserving_rigidMotion u a).measure_preimage
    Metric.isOpen_thickening.measurableSet.nullMeasurableSet).symm

/--
@isnad1 id=eq.0h5v.s16.8b7cd370bdb4 from=translated src=- shape=2a91a0fb vocab=10decae2
-/
theorem preimage_unitDisk_rotate (u : Rotations n) (a : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) :
    Unitary.linearIsometryEquiv u ⁻¹' unitDisk (Grassmannian.rotate u V).val
      (Unitary.linearIsometryEquiv u a) = unitDisk V.val a := by
  ext x
  simp only [Set.mem_preimage, unitDisk, Set.mem_ofPred_eq, ← map_sub,
    LinearIsometryEquiv.norm_map]
  apply and_congr_left
  intro _
  change Unitary.linearIsometryEquiv u (x - a) ∈
    Unitary.linearIsometryEquiv u '' (V.val : Set (EuclideanSpace ℝ (Fin n))) ↔
      x - a ∈ (V.val : Set (EuclideanSpace ℝ (Fin n)))
  simp only [Set.mem_image, (Unitary.linearIsometryEquiv u).injective.eq_iff, exists_eq_right]

/--
@isnad1 id=eq.0h6v.s16.d9f77dd8c2d3 from=translated src=- shape=b0d7a006 vocab=61d9f77b
-/
theorem preimage_plate_rotate (u : Rotations n) (a : EuclideanSpace ℝ (Fin n))
    (V : Grassmannian n k) (δ : ℝ) :
    Unitary.linearIsometryEquiv u ⁻¹' plate δ (Grassmannian.rotate u V).val
      (Unitary.linearIsometryEquiv u a) = plate δ V.val a := by
  have himage : Unitary.linearIsometryEquiv u '' unitDisk V.val a =
      unitDisk (Grassmannian.rotate u V).val (Unitary.linearIsometryEquiv u a) := by
    rw [← preimage_unitDisk_rotate]
    exact (Unitary.linearIsometryEquiv u).surjective.image_preimage _
  rw [plate, ← himage]
  ext x
  simp only [Set.mem_preimage, plate, Metric.mem_thickening_iff_infEDist_lt,
    Metric.infEDist_image (Unitary.linearIsometryEquiv u).isometry]

end NKBesicovitch
