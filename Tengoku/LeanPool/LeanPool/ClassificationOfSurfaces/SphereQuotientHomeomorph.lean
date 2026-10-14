/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.SphereHemisphere
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.SphereCarrierGeometry
public import Tengoku

/-!
# The two-monogon quotient is the standard sphere

The facewise hemisphere map from `SphereHemisphere` respects the equivalence relation generated
by the sphere's side pairing, so it descends to the polygonal realization.  This file proves that
the descended map is bijective and hence, by compactness of the source and the Hausdorff property
of the target, a homeomorphism with `SphereRepresentative`.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Complex
open scoped ComplexConjugate

namespace PolygonCell

/-- The upper hemisphere parameterization remembers its disk point.
@isnad1 id=injectiv.0h0v.s9.9ad94a7a108f from=translated src=- shape=ac9758f7 vocab=0dab4a33
-/
theorem upperHemisphere_injective : Function.Injective upperHemisphere := by
  intro z w hzw
  apply PolygonCell.ext
  apply Complex.ext
  · simpa [upperHemisphere, upperHemisphereVector] using
      congrArg (fun x : SphereRepresentative ↦ x.val 0) hzw
  · simpa [upperHemisphere, upperHemisphereVector] using
      congrArg (fun x : SphereRepresentative ↦ x.val 1) hzw

/-- The lower hemisphere parameterization remembers its disk point.
@isnad1 id=injectiv.0h0v.s9.cfc2d8db8bc4 from=translated src=- shape=ac9758f7 vocab=01a8e55d
-/
theorem lowerHemisphere_injective : Function.Injective lowerHemisphere := by
  intro z w hzw
  apply PolygonCell.ext
  have hconj : conj z.val = conj w.val := by
    apply Complex.ext
    · simpa [lowerHemisphere, lowerHemisphereVector] using
        congrArg (fun x : SphereRepresentative ↦ x.val 0) hzw
    · simpa [lowerHemisphere, lowerHemisphereVector] using
        congrArg (fun x : SphereRepresentative ↦ x.val 1) hzw
  simpa using congrArg conj hconj

/-- Zero hemisphere height means that the disk point lies on its boundary circle.
@isnad1 id=mem.1h2v.s5.f3fe7feaf4e5 from=translated src=- shape=3da9caf2 vocab=f86b0fc4
-/
theorem mem_sphere_of_hemisphereHeight_eq_zero {n : ℕ} (z : PolygonCell n)
    (hz : hemisphereHeight z = 0) :
    z.val ∈ Metric.sphere 0 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hsquare := hemisphereHeight_sq z
  norm_num [hz, Complex.normSq_eq_norm_sq] at hsquare
  nlinarith [norm_nonneg z.val]

/-- The horizontal coordinates of a point on the standard sphere, regarded as a disk point. -/
noncomputable def sphereDiskPoint (x : SphereRepresentative) : PolygonCell 1 :=
  ⟨Complex.mk (x.val 0) (x.val 1), by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    have hnorm := mem_sphere_zero_iff_norm.mp x.property
    have hsquare := congrArg (fun r : ℝ ↦ r ^ 2) hnorm
    rw [EuclideanSpace.real_norm_sq_eq] at hsquare
    have hsum : x.val 0 ^ 2 + x.val 1 ^ 2 + x.val 2 ^ 2 = 1 := by
      simp [Fin.sum_univ_succ] at hsquare
      nlinarith
    rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num)]
    rw [Complex.sq_norm, Complex.normSq_mk]
    nlinarith [sq_nonneg (x.val 2)]⟩

/--
@isnad1 id=eq.0h1v.s8.c65c4783650e from=translated src=- shape=e344df0b vocab=b96a5081
-/
@[simp]
theorem sphereDiskPoint_re (x : SphereRepresentative) :
    (sphereDiskPoint x).val.re = x.val 0 :=
  rfl

/--
@isnad1 id=eq.0h1v.s8.43177f99bae7 from=translated src=- shape=e344df0b vocab=d3dcadbc
-/
@[simp]
theorem sphereDiskPoint_im (x : SphereRepresentative) :
    (sphereDiskPoint x).val.im = x.val 1 :=
  rfl

/-- The height recovered from the horizontal coordinates is the absolute vertical coordinate.
@isnad1 id=eq.0h1v.s8.34d177bcd86f from=translated src=- shape=57a2004a vocab=5d9f6ba8
-/
@[simp]
theorem hemisphereHeight_sphereDiskPoint (x : SphereRepresentative) :
    hemisphereHeight (sphereDiskPoint x) = |x.val 2| := by
  unfold hemisphereHeight
  have hnorm := mem_sphere_zero_iff_norm.mp x.property
  have hsquare := congrArg (fun r : ℝ ↦ r ^ 2) hnorm
  rw [EuclideanSpace.real_norm_sq_eq] at hsquare
  have hsum : x.val 0 ^ 2 + x.val 1 ^ 2 + x.val 2 ^ 2 = 1 := by
    simp [Fin.sum_univ_succ] at hsquare
    nlinarith
  rw [show 1 - Complex.normSq (sphereDiskPoint x).val = x.val 2 ^ 2 by
    rw [Complex.normSq_apply]
    simp only [sphereDiskPoint_re, sphereDiskPoint_im]
    nlinarith]
  exact Real.sqrt_sq_eq_abs _

/-- Complex conjugation does not change the height assigned to a disk point.
@isnad1 id=eq.0h2v.s5.ee4bc37d8233 from=translated src=- shape=5ee4dc30 vocab=49a261cf
-/
@[simp]
theorem hemisphereHeight_conjHomeomorph {n : ℕ} (z : PolygonCell n) :
    hemisphereHeight (conjHomeomorph n z) = hemisphereHeight z := by
  simp [hemisphereHeight, Complex.normSq_conj]

/-- A sphere point with nonnegative vertical coordinate is hit by the upper hemisphere.
@isnad1 id=eq.1h1v.s9.1232910dc77e from=translated src=- shape=e1777ae7 vocab=4f8f6b92
-/
theorem upperHemisphere_sphereDiskPoint (x : SphereRepresentative) (hx : 0 ≤ x.val 2) :
    upperHemisphere (sphereDiskPoint x) = x := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [upperHemisphere, upperHemisphereVector, abs_of_nonneg hx]

/-- A sphere point with nonpositive vertical coordinate is hit by the conjugated lower face.
@isnad1 id=eq.1h1v.s10.e2f72c54b7d8 from=translated src=- shape=d3e1b4f1 vocab=352ad4ca
-/
theorem lowerHemisphere_conj_sphereDiskPoint (x : SphereRepresentative) (hx : x.val 2 ≤ 0) :
    lowerHemisphere (conjHomeomorph 1 (sphereDiskPoint x)) = x := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [lowerHemisphere, lowerHemisphereVector, abs_of_nonpos hx]

end PolygonCell

namespace SurfaceCellComplex

/-- The sphere pre-map is constant on the equivalence relation generated by the side pairing.
@isnad1 id=eq.1h2v.s10.cd99f20a36d7 from=translated src=- shape=e23ede7f vocab=21f8fc15
-/
theorem spherePreMap_eq_of_gluingRel
    {x y : sphere.PolygonalPreRealization}
    (hxy : sphere.PolygonalGluingRel sphere_occurrencePairingValid x y) :
    spherePreMap x = spherePreMap y := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      (sphere.polygonalIdentifications sphere_occurrencePairingValid)) x y at hxy
  induction hxy with
  | rel _ _ h => exact spherePreMap_eq_of_generator h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz

/-- The continuous sphere map descended from the two monogon faces to their polygonal quotient. -/
noncomputable def sphereQuotientMap :
    C(sphere.PolygonalRealization sphere_occurrencePairingValid, SphereRepresentative) where
  toFun := Quotient.lift spherePreMap fun _ _ hxy ↦ spherePreMap_eq_of_gluingRel hxy
  continuous_toFun :=
    spherePreMap.continuous.quotient_lift fun _ _ hxy ↦ spherePreMap_eq_of_gluingRel hxy

/--
@isnad1 id=eq.0h1v.s10.7a3d1dd4578e from=translated src=- shape=fe59ab87 vocab=9c696b9f
-/
@[simp]
theorem sphereQuotientMap_polygonalMk (x : sphere.PolygonalPreRealization) :
    sphereQuotientMap (sphere.polygonalMk sphere_occurrencePairingValid x) = spherePreMap x :=
  rfl

/-- Equality between an upper- and a lower-hemisphere image is exactly an equatorial gluing.
@isnad1 id=r.1h2v.s10.dc7a0169ded5 from=translated src=- shape=3d17983c vocab=a29d9325
-/
theorem sphereGluingRel_of_upperHemisphere_eq_lowerHemisphere
    (z w : PolygonCell 1)
    (hzw : PolygonCell.upperHemisphere z = PolygonCell.lowerHemisphere w) :
    sphere.PolygonalGluingRel sphere_occurrencePairingValid
      ⟨false, z⟩ ⟨true, w⟩ := by
  have hheight :
      PolygonCell.hemisphereHeight z = -PolygonCell.hemisphereHeight w := by
    simpa [PolygonCell.upperHemisphere, PolygonCell.lowerHemisphere,
      PolygonCell.upperHemisphereVector, PolygonCell.lowerHemisphereVector] using
      congrArg (fun x : SphereRepresentative ↦ x.val 2) hzw
  have hzheight : PolygonCell.hemisphereHeight z = 0 := by
    nlinarith [PolygonCell.hemisphereHeight_nonneg z,
      PolygonCell.hemisphereHeight_nonneg w]
  obtain ⟨i, t, hit⟩ :=
    PolygonCell.exists_side_eq_of_mem_sphere (n := 1) (by decide) z
      (PolygonCell.mem_sphere_of_hemisphereHeight_eq_zero z hzheight)
  have hi : i = 0 := Fin.eq_zero i
  subst i
  have hcomplex :
      (PolygonCell.side (0 : Fin 1) t : PolygonCell 1).val = conj w.val := by
    rw [hit]
    apply Complex.ext
    · simpa [PolygonCell.upperHemisphere, PolygonCell.lowerHemisphere,
        PolygonCell.upperHemisphereVector, PolygonCell.lowerHemisphereVector] using
        congrArg (fun x : SphereRepresentative ↦ x.val 0) hzw
    · simpa [PolygonCell.upperHemisphere, PolygonCell.lowerHemisphere,
        PolygonCell.upperHemisphereVector, PolygonCell.lowerHemisphereVector] using
        congrArg (fun x : SphereRepresentative ↦ x.val 1) hzw
  have hw :
      w = PolygonCell.side (0 : Fin 1) (unitInterval.symm t) := by
    apply PolygonCell.ext
    have hconj := congrArg conj hcomplex
    rw [Complex.conj_conj] at hconj
    have hside :
        conj ((PolygonCell.side (0 : Fin 1) t : PolygonCell 1).val) =
          (PolygonCell.side (0 : Fin 1) (unitInterval.symm t) : PolygonCell 1).val := by
      simpa only [unitInterval.symm_symm] using
        PolygonCell.conj_side_symm_monogon (unitInterval.symm t)
    exact hconj.symm.trans hside
  rw [← hit, hw]
  exact PolygonGluing.related_of_mem sphereBoundaryPairing.identification
    sphereBoundaryPairing_mem t

/-- Equal images under the facewise map are related by the generated sphere gluing relation.
@isnad1 id=r.1h2v.s10.41e35a7c3cc6 from=translated src=- shape=48c6ae92 vocab=21f8fc15
-/
theorem sphereGluingRel_of_spherePreMap_eq
    {x y : sphere.PolygonalPreRealization}
    (hxy : spherePreMap x = spherePreMap y) :
    sphere.PolygonalGluingRel sphere_occurrencePairingValid x y := by
  rcases x with ⟨face, z⟩
  rcases y with ⟨face', w⟩
  cases face <;> cases face'
  · have hzw : z = w := PolygonCell.upperHemisphere_injective (by simpa using hxy)
    subst w
    exact Relation.EqvGen.refl _
  · exact sphereGluingRel_of_upperHemisphere_eq_lowerHemisphere z w (by simpa using hxy)
  · exact Relation.EqvGen.symm _ _
      (sphereGluingRel_of_upperHemisphere_eq_lowerHemisphere w z (by simpa using hxy.symm))
  · have hzw : z = w := PolygonCell.lowerHemisphere_injective (by simpa using hxy)
    subst w
    exact Relation.EqvGen.refl _

/-- The generated sphere gluing relation is precisely the kernel relation of the pre-map.
@isnad1 id=iff.0h2v.s10.c1c19e7724d7 from=translated src=- shape=aa8229e5 vocab=21f8fc15
-/
theorem spherePreMap_eq_iff_gluingRel
    {x y : sphere.PolygonalPreRealization} :
    spherePreMap x = spherePreMap y ↔
      sphere.PolygonalGluingRel sphere_occurrencePairingValid x y :=
  ⟨sphereGluingRel_of_spherePreMap_eq, spherePreMap_eq_of_gluingRel⟩

/-- The descended sphere map is injective.
@isnad1 id=injectiv.0h0v.s9.1f89ed168361 from=translated src=- shape=e9b5d3b4 vocab=1570fbff
-/
theorem sphereQuotientMap_injective : Function.Injective sphereQuotientMap := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
          apply Quotient.sound
          apply sphereGluingRel_of_spherePreMap_eq
          change spherePreMap x = spherePreMap y at hqr
          exact hqr

/-- Every point of the standard sphere is hit by the descended two-monogon map.
@isnad1 id=surjecti.0h0v.s9.2e6be783ac29 from=translated src=- shape=e9b5d3b4 vocab=4eaf9c3a
-/
theorem sphereQuotientMap_surjective : Function.Surjective sphereQuotientMap := by
  intro x
  by_cases hx : 0 ≤ x.val 2
  · refine ⟨sphere.polygonalMk sphere_occurrencePairingValid
        ⟨false, PolygonCell.sphereDiskPoint x⟩, ?_⟩
    change PolygonCell.upperHemisphere (PolygonCell.sphereDiskPoint x) = x
    exact PolygonCell.upperHemisphere_sphereDiskPoint x hx
  · have hx' : x.val 2 ≤ 0 := le_of_not_ge hx
    refine ⟨sphere.polygonalMk sphere_occurrencePairingValid
        ⟨true, PolygonCell.conjHomeomorph 1 (PolygonCell.sphereDiskPoint x)⟩, ?_⟩
    change
      PolygonCell.lowerHemisphere
        (PolygonCell.conjHomeomorph 1 (PolygonCell.sphereDiskPoint x)) = x
    exact PolygonCell.lowerHemisphere_conj_sphereDiskPoint x hx'

/-- The descended sphere map is bijective.
@isnad1 id=bijectiv.0h0v.s9.d325a6f59eed from=translated src=- shape=e9b5d3b4 vocab=c0257767
-/
theorem sphereQuotientMap_bijective : Function.Bijective sphereQuotientMap :=
  ⟨sphereQuotientMap_injective, sphereQuotientMap_surjective⟩

/-- The underlying equivalence of the two-monogon quotient with the standard sphere. -/
noncomputable def spherePolygonalRealizationEquiv :
    sphere.PolygonalRealization sphere_occurrencePairingValid ≃ SphereRepresentative :=
  Equiv.ofBijective sphereQuotientMap sphereQuotientMap_bijective

/--
@isnad1 id=eq.0h1v.s9.5a3a61876685 from=translated src=- shape=ae8a2b56 vocab=f422894d
-/
@[simp]
theorem spherePolygonalRealizationEquiv_apply
    (q : sphere.PolygonalRealization sphere_occurrencePairingValid) :
    spherePolygonalRealizationEquiv q = sphereQuotientMap q :=
  rfl

/-- The polygonal realization of the two-monogon presentation is the standard two-sphere. -/
noncomputable def spherePolygonalRealizationHomeomorph :
    sphere.PolygonalRealization sphere_occurrencePairingValid ≃ₜ SphereRepresentative :=
  Continuous.homeoOfEquivCompactToT2
    (f := spherePolygonalRealizationEquiv) sphereQuotientMap.continuous

/--
@isnad1 id=eq.0h1v.s10.9c1d4548db0b from=translated src=- shape=ae8a2b56 vocab=b371f39d
-/
@[simp]
theorem spherePolygonalRealizationHomeomorph_apply
    (q : sphere.PolygonalRealization sphere_occurrencePairingValid) :
    spherePolygonalRealizationHomeomorph q = sphereQuotientMap q :=
  rfl

/--
@isnad1 id=eq.0h1v.s10.46b60ccef939 from=translated src=- shape=5fb17b5a vocab=2753dfe7
-/
@[simp]
theorem spherePolygonalRealizationHomeomorph_polygonalMk
    (x : sphere.PolygonalPreRealization) :
    spherePolygonalRealizationHomeomorph
        (sphere.polygonalMk sphere_occurrencePairingValid x) =
      spherePreMap x :=
  rfl

end SurfaceCellComplex

end ClassificationOfSurfaces
end Topology
end LeanEval
