/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Geometry.SphereRotations
public import Tengoku.Seed.MeasureTheory.Constructions.HaarToSphere
public import Tengoku.Seed.MeasureTheory.Measure.Haar.InnerProductSpace
public import Tengoku.Seed.MeasureTheory.Measure.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Haar-distributed directions and Euclidean sphere measure

Rotating a fixed unit vector by a Haar-distributed orthogonal operator
gives normalized surface measure. The cone formula proves invariance of
surface measure, and transitivity identifies the invariant probability.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace NKBesicovitch.Rotations

variable {n : ℕ}

/--
@isnad1 id=measurab.0h2v.s12.f8a8c2b8251a from=translated src=- shape=75c1144c vocab=7aa4d107
-/
theorem measurable_sphereOrbit (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measurable (fun u : Rotations n ↦ rotateSphere u v) :=
  (continuous_rotateSphere.comp (continuous_id.prodMk continuous_const)).measurable

/--
@isnad1 id=eq.0h3v.s15.f64175f8b264 from=translated src=- shape=f44ce535 vocab=e139c830
-/
theorem preimage_sphereCone_rotate (u : Rotations n)
    (s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    (Unitary.linearIsometryEquiv u) ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0 : ℝ) 1 • (Subtype.val '' (rotateSphere u ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨w, hw, rfl⟩, h⟩
    have heq : rotateSphere u (rotateSphere u⁻¹ w) = w := by
      rw [← rotateSphere_mul, mul_inv_cancel, rotateSphere_one]
    refine ⟨a, ha, _, ⟨rotateSphere u⁻¹ w, ?_, rfl⟩, ?_⟩
    · change rotateSphere u (rotateSphere u⁻¹ w) ∈ s
      rwa [heq]
    · apply (Unitary.linearIsometryEquiv u).injective
      change Unitary.linearIsometryEquiv u
        (a • (rotateSphere u⁻¹ w : EuclideanSpace ℝ (Fin n))) = _
      rw [map_smul]
      change a • (rotateSphere u (rotateSphere u⁻¹ w) : EuclideanSpace ℝ (Fin n)) = _
      simpa only [heq] using h
  · rintro ⟨a, ha, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨a, ha, _, ⟨rotateSphere u w, hw, rfl⟩, ?_⟩
    exact (map_smul (Unitary.linearIsometryEquiv u) a
      (w : EuclideanSpace ℝ (Fin n))).symm

/--
@isnad1 id=measurep.0h2v.s12.018b1670bc32 from=translated src=- shape=e99838e6 vocab=20e77e9d
-/
theorem measurePreserving_rotateSphere (u : Rotations n) :
    MeasurePreserving (rotateSphere u)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  have hm : Measurable (rotateSphere u) :=
    (continuous_rotateSphere.comp (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hm, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' _ (hs.preimage hm),
    Measure.toSphere_apply' _ hs, ← preimage_sphereCone_rotate]
  congr 1
  exact (Unitary.linearIsometryEquiv u).measurePreserving.measure_preimage_emb
    (Unitary.linearIsometryEquiv u).toHomeomorph.measurableEmbedding _

end NKBesicovitch.Rotations
