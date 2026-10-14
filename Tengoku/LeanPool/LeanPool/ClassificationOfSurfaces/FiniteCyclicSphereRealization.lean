/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicCanonical
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicRealization
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.SphereQuotientHomeomorph
public import Tengoku

/-!
# The canonical finite-cyclic sphere realization

This file compares the finite-cyclic two-monogon presentation with the existing typed
two-monogon presentation and transports the already established sphere homeomorphism across that
comparison.
-/

@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

/-- The two faces of the finite-cyclic sphere, in the order used by the typed sphere model. -/
def twoMonogonFaceEquiv : twoMonogonSphere.Face ≃ Bool where
  toFun f := if f = 0 then false else true
  invFun b := if b then 1 else 0
  left_inv := by
    intro f
    fin_cases f <;> simp
  right_inv := by
    intro b
    cases b <;> simp

/--
@isnad1 id=eq.0h0v.s5.79302fd6eca9 from=translated src=- shape=4e0f1cd4 vocab=40524525
-/
@[simp]
theorem twoMonogonFaceEquiv_zero : twoMonogonFaceEquiv 0 = false := by
  rfl

/--
@isnad1 id=eq.0h0v.s5.14a0374a4f9b from=translated src=- shape=4e0f1cd4 vocab=0afe6ecf
-/
@[simp]
theorem twoMonogonFaceEquiv_one : twoMonogonFaceEquiv 1 = true := by
  rfl

/-- Corresponding monogon faces have the same side count.
@isnad1 id=eq.0h1v.s5.b5d7727ed74f from=translated src=- shape=bf1e465a vocab=c482ef3c
-/
theorem twoMonogon_faceBoundaryLength_eq (f : twoMonogonSphere.Face) :
    (twoMonogonSphere.boundary f).length =
      SurfaceCellComplex.sphere.faceBoundaryLength (twoMonogonFaceEquiv f) := by
  fin_cases f <;> rfl

/-- The identity disk map, with its side-count index transported to the typed sphere model. -/
noncomputable def twoMonogonFaceHomeomorph (f : twoMonogonSphere.Face) :
    PolygonCell (twoMonogonSphere.boundary f).length ≃ₜ
      PolygonCell (SurfaceCellComplex.sphere.faceBoundaryLength
        (twoMonogonFaceEquiv f)) where
  toFun z := ⟨z.val, z.property⟩
  invFun z := ⟨z.val, z.property⟩
  left_inv := fun _ => PolygonCell.ext rfl
  right_inv := fun _ => PolygonCell.ext rfl
  continuous_toFun :=
    continuous_induced_rng.2 PolygonCell.continuous_val
  continuous_invFun :=
    continuous_induced_rng.2 PolygonCell.continuous_val

/-- Relabel the two finite-cyclic monogon faces by `Bool`, leaving both disks fixed. -/
noncomputable def twoMonogonPreHomeomorph :
    twoMonogonSphere.PolygonalPreRealization ≃ₜ
      SurfaceCellComplex.sphere.PolygonalPreRealization :=
  (IsHomeomorph.sigmaMap twoMonogonFaceEquiv.bijective
      (fun f => (twoMonogonFaceHomeomorph f).isHomeomorph)).homeomorph
    (Sigma.map twoMonogonFaceEquiv fun f => twoMonogonFaceHomeomorph f)

/--
@isnad1 id=eq.0h1v.s7.0843a5ba8662 from=translated src=- shape=6281ecb7 vocab=0d942c49
-/
@[simp]
theorem twoMonogonPreHomeomorph_zero (z : PolygonCell 1) :
    twoMonogonPreHomeomorph ⟨(0 : twoMonogonSphere.Face), z⟩ =
      ⟨false, z⟩ := by
  apply Sigma.ext
  · rfl
  · exact HEq.rfl

/--
@isnad1 id=eq.0h1v.s7.120c1a8ef0a6 from=translated src=- shape=6281ecb7 vocab=ccad722a
-/
@[simp]
theorem twoMonogonPreHomeomorph_one (z : PolygonCell 1) :
    twoMonogonPreHomeomorph ⟨(1 : twoMonogonSphere.Face), z⟩ =
      ⟨true, z⟩ := by
  apply Sigma.ext
  · rfl
  · exact HEq.rfl

/--
@isnad1 id=eq.0h1v.s8.64a396fd7386 from=translated src=- shape=27c562bd vocab=3718a853
-/
@[simp]
theorem twoMonogonPreHomeomorph_symm_false (z : PolygonCell 1) :
    twoMonogonPreHomeomorph.symm ⟨false, z⟩ =
      ⟨(0 : twoMonogonSphere.Face), z⟩ := by
  apply twoMonogonPreHomeomorph.injective
  simp

/--
@isnad1 id=eq.0h1v.s8.9f8ee46da0c9 from=translated src=- shape=27c562bd vocab=3337ffcc
-/
@[simp]
theorem twoMonogonPreHomeomorph_symm_true (z : PolygonCell 1) :
    twoMonogonPreHomeomorph.symm ⟨true, z⟩ =
      ⟨(1 : twoMonogonSphere.Face), z⟩ := by
  apply twoMonogonPreHomeomorph.injective
  simp

/-- The positive monogon occurrence in the finite-cyclic sphere. -/
def twoMonogonPositiveOccurrence : twoMonogonSphere.BoundaryOccurrence :=
  ⟨0, ⟨0, by simp [twoMonogonSphere, boundary]⟩⟩

/-- The negative monogon occurrence in the finite-cyclic sphere. -/
def twoMonogonNegativeOccurrence : twoMonogonSphere.BoundaryOccurrence :=
  ⟨1, ⟨0, by simp [twoMonogonSphere, boundary]⟩⟩

/--
@isnad1 id=eq.0h0v.s4.3b4440caa016 from=translated src=- shape=d256f35a vocab=daf37b90
-/
@[simp]
theorem twoMonogonPositiveOccurrence_dart :
    twoMonogonPositiveOccurrence.dart = .pos 0 :=
  by simp [twoMonogonPositiveOccurrence, BoundaryOccurrence.dart,
    twoMonogonSphere, boundary]

/--
@isnad1 id=eq.0h0v.s4.9c27429aadf1 from=translated src=- shape=d256f35a vocab=5951b713
-/
@[simp]
theorem twoMonogonNegativeOccurrence_dart :
    twoMonogonNegativeOccurrence.dart = .neg 0 :=
  by simp [twoMonogonNegativeOccurrence, BoundaryOccurrence.dart,
    twoMonogonSphere, boundary]

/-- Every boundary occurrence of the finite-cyclic sphere is one of its two monogon sides.
@isnad1 id=or.0h1v.s3.2bdd60485800 from=translated src=- shape=3078c585 vocab=fa8cdfe8
-/
theorem twoMonogonBoundaryOccurrence_eq
    (occurrence : twoMonogonSphere.BoundaryOccurrence) :
    occurrence = twoMonogonPositiveOccurrence ∨
      occurrence = twoMonogonNegativeOccurrence := by
  rcases occurrence with ⟨face, index⟩
  fin_cases face
  · change Fin 1 at index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    left
    apply Sigma.ext
    · rfl
    · exact HEq.rfl
  · change Fin 1 at index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    right
    apply Sigma.ext
    · rfl
    · exact HEq.rfl

/--
@isnad1 id=not.0h1v.s2.e942454c97d3 from=translated src=- shape=17bc9619 vocab=285bbca9
-/
theorem twoMonogon_not_isBoundaryEdge (e : twoMonogonSphere.Edge) :
    ¬twoMonogonSphere.IsBoundaryEdge e := by
  intro h
  rw [IsBoundaryEdge, twoMonogonSphere_edgeMultiplicity] at h
  omega

/-- The directed positive-to-negative side pairing of the finite-cyclic sphere. -/
def twoMonogonBoundaryPairing : twoMonogonSphere.BoundaryPairing where
  source := twoMonogonPositiveOccurrence
  target := twoMonogonNegativeOccurrence
  source_ne_target := by
    simp [twoMonogonPositiveOccurrence, twoMonogonNegativeOccurrence]
  source_not_boundary := twoMonogon_not_isBoundaryEdge _
  target_not_boundary := twoMonogon_not_isBoundaryEdge _
  direction := .opposite
  compatible := by simp [SurfaceCellComplex.SignedDart.flip]

/-- The reverse directed form of the unique finite-cyclic sphere pairing. -/
def twoMonogonReverseBoundaryPairing : twoMonogonSphere.BoundaryPairing where
  source := twoMonogonNegativeOccurrence
  target := twoMonogonPositiveOccurrence
  source_ne_target := by
    simp [twoMonogonPositiveOccurrence, twoMonogonNegativeOccurrence]
  source_not_boundary := twoMonogon_not_isBoundaryEdge _
  target_not_boundary := twoMonogon_not_isBoundaryEdge _
  direction := .opposite
  compatible := by simp [SurfaceCellComplex.SignedDart.flip]

/--
@isnad1 id=mem.0h0v.s5.d6246fe04fe0 from=translated src=- shape=f589a2a3 vocab=03c66971
-/
theorem twoMonogonBoundaryPairing_mem :
    twoMonogonBoundaryPairing.identification ∈
      twoMonogonSphere.polygonalIdentifications
        twoMonogonSphere_isSurfaceValid :=
  pairing_identification_mem _ _

/--
@isnad1 id=mem.0h0v.s5.03d76494b04a from=translated src=- shape=f589a2a3 vocab=edb3594f
-/
theorem twoMonogonReverseBoundaryPairing_mem :
    twoMonogonReverseBoundaryPairing.identification ∈
      twoMonogonSphere.polygonalIdentifications
        twoMonogonSphere_isSurfaceValid :=
  pairing_identification_mem _ _

/-- The two directed forms of the monogon pairing exhaust the finite-cyclic sphere generators.
@isnad1 id=iff.0h1v.s6.39bb5f1d92dd from=translated src=- shape=73edceeb vocab=baf48358
-/
theorem mem_twoMonogon_polygonalIdentifications_iff
    (identification :
      PolygonGluing.Identification twoMonogonSphere.Face
        fun f => (twoMonogonSphere.boundary f).length) :
    identification ∈
        twoMonogonSphere.polygonalIdentifications
          twoMonogonSphere_isSurfaceValid ↔
      identification = twoMonogonBoundaryPairing.identification ∨
        identification = twoMonogonReverseBoundaryPairing.identification := by
  change identification ∈ Set.range BoundaryPairing.identification ↔ _
  constructor
  · rintro
      ⟨⟨source, target, hne, _hsource, _htarget, direction, hcompatible⟩, rfl⟩
    rcases twoMonogonBoundaryOccurrence_eq source with rfl | rfl
    · rcases twoMonogonBoundaryOccurrence_eq target with rfl | rfl
      · exact (hne rfl).elim
      · cases direction with
        | same => simp at hcompatible
        | opposite => exact Or.inl rfl
    · rcases twoMonogonBoundaryOccurrence_eq target with rfl | rfl
      · cases direction with
        | same => simp at hcompatible
        | opposite => exact Or.inr rfl
      · exact (hne rfl).elim
  · rintro (rfl | rfl)
    · exact twoMonogonBoundaryPairing_mem
    · exact twoMonogonReverseBoundaryPairing_mem

/--
@isnad1 id=eq.0h1v.s7.63a06246a212 from=translated src=- shape=b917dcc2 vocab=892b20c2
-/
theorem twoMonogonPreHomeomorph_boundaryPairing_source
    (t : unitInterval) :
    twoMonogonPreHomeomorph
        (twoMonogonBoundaryPairing.identification.source.point t) =
      SurfaceCellComplex.sphereBoundaryPairing.identification.source.point t := by
  simp [twoMonogonBoundaryPairing, twoMonogonPositiveOccurrence,
    SurfaceCellComplex.sphereBoundaryPairing,
    SurfaceCellComplex.spherePositiveOccurrence, occurrenceSide,
    SurfaceCellComplex.occurrenceSide, PolygonGluing.Side.point]
  congr 2

/--
@isnad1 id=eq.0h1v.s7.f08b4ac3b81f from=translated src=- shape=b917dcc2 vocab=7b5fd71b
-/
theorem twoMonogonPreHomeomorph_boundaryPairing_target
    (t : unitInterval) :
    twoMonogonPreHomeomorph
        (twoMonogonBoundaryPairing.identification.target.point t) =
      SurfaceCellComplex.sphereBoundaryPairing.identification.target.point t := by
  simp [twoMonogonBoundaryPairing, twoMonogonNegativeOccurrence,
    SurfaceCellComplex.sphereBoundaryPairing,
    SurfaceCellComplex.sphereNegativeOccurrence, occurrenceSide,
    SurfaceCellComplex.occurrenceSide, PolygonGluing.Side.point]
  congr 2

/--
@isnad1 id=eq.0h1v.s7.a446f65a25e5 from=translated src=- shape=5286e1bd vocab=2c343aa8
-/
theorem twoMonogonPreHomeomorph_reverseBoundaryPairing_source
    (t : unitInterval) :
    twoMonogonPreHomeomorph
        (twoMonogonReverseBoundaryPairing.identification.source.point t) =
      (SurfaceCellComplex.swapIdentification
        SurfaceCellComplex.sphereBoundaryPairing.identification).source.point t := by
  simp [twoMonogonReverseBoundaryPairing, twoMonogonNegativeOccurrence,
    SurfaceCellComplex.swapIdentification,
    SurfaceCellComplex.sphereBoundaryPairing,
    SurfaceCellComplex.sphereNegativeOccurrence, occurrenceSide,
    SurfaceCellComplex.occurrenceSide, PolygonGluing.Side.point]
  congr 2

/--
@isnad1 id=eq.0h1v.s7.5dd6b3820d4f from=translated src=- shape=5286e1bd vocab=3793c6cc
-/
theorem twoMonogonPreHomeomorph_reverseBoundaryPairing_target
    (t : unitInterval) :
    twoMonogonPreHomeomorph
        (twoMonogonReverseBoundaryPairing.identification.target.point t) =
      (SurfaceCellComplex.swapIdentification
        SurfaceCellComplex.sphereBoundaryPairing.identification).target.point t := by
  simp [twoMonogonReverseBoundaryPairing, twoMonogonPositiveOccurrence,
    SurfaceCellComplex.swapIdentification,
    SurfaceCellComplex.sphereBoundaryPairing,
    SurfaceCellComplex.spherePositiveOccurrence, occurrenceSide,
    SurfaceCellComplex.occurrenceSide, PolygonGluing.Side.point]
  congr 2

/-- Relabeling the two monogon faces sends the finite-cyclic gluing relation into the typed
sphere gluing relation.
@isnad1 id=r.1h2v.s8.230e3636adca from=translated src=- shape=ddfa3dcf vocab=8e96b272
-/
theorem twoMonogonPreHomeomorph_related
    {x y : twoMonogonSphere.PolygonalPreRealization}
    (hxy :
      twoMonogonSphere.PolygonalGluingRel
        twoMonogonSphere_isSurfaceValid x y) :
    SurfaceCellComplex.sphere.PolygonalGluingRel
      SurfaceCellComplex.sphere_occurrencePairingValid
      (twoMonogonPreHomeomorph x) (twoMonogonPreHomeomorph y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      (twoMonogonSphere.polygonalIdentifications
        twoMonogonSphere_isSurfaceValid)) x y at hxy
  change Relation.EqvGen
    (PolygonGluing.Generator
      (SurfaceCellComplex.sphere.polygonalIdentifications
        SurfaceCellComplex.sphere_occurrencePairingValid))
      (twoMonogonPreHomeomorph x) (twoMonogonPreHomeomorph y)
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hidentification t =>
          rw [mem_twoMonogon_polygonalIdentifications_iff] at hidentification
          rcases hidentification with rfl | rfl
          · rw [twoMonogonPreHomeomorph_boundaryPairing_source,
              twoMonogonPreHomeomorph_boundaryPairing_target]
            exact PolygonGluing.related_of_mem
              SurfaceCellComplex.sphereBoundaryPairing.identification
              SurfaceCellComplex.sphereBoundaryPairing_mem t
          · rw [twoMonogonPreHomeomorph_reverseBoundaryPairing_source,
              twoMonogonPreHomeomorph_reverseBoundaryPairing_target]
            exact PolygonGluing.related_of_mem
              (SurfaceCellComplex.swapIdentification
                SurfaceCellComplex.sphereBoundaryPairing.identification)
              (SurfaceCellComplex.swapIdentification_mem_polygonalIdentifications
                SurfaceCellComplex.sphere_occurrencePairingValid
                SurfaceCellComplex.sphereBoundaryPairing_mem) t
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The inverse face relabeling sends the typed sphere gluing relation back into the
finite-cyclic gluing relation.
@isnad1 id=r.1h2v.s8.f1bff576331b from=translated src=- shape=efea9ac4 vocab=836f0f3e
-/
theorem twoMonogonPreHomeomorph_symm_related
    {x y : SurfaceCellComplex.sphere.PolygonalPreRealization}
    (hxy :
      SurfaceCellComplex.sphere.PolygonalGluingRel
        SurfaceCellComplex.sphere_occurrencePairingValid x y) :
    twoMonogonSphere.PolygonalGluingRel
      twoMonogonSphere_isSurfaceValid
      (twoMonogonPreHomeomorph.symm x)
      (twoMonogonPreHomeomorph.symm y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      (SurfaceCellComplex.sphere.polygonalIdentifications
        SurfaceCellComplex.sphere_occurrencePairingValid)) x y at hxy
  change Relation.EqvGen
    (PolygonGluing.Generator
      (twoMonogonSphere.polygonalIdentifications
        twoMonogonSphere_isSurfaceValid))
      (twoMonogonPreHomeomorph.symm x)
      (twoMonogonPreHomeomorph.symm y)
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hidentification t =>
          rw [SurfaceCellComplex.mem_sphere_polygonalIdentifications_iff] at hidentification
          rcases hidentification with rfl | rfl
          · rw [← twoMonogonPreHomeomorph_boundaryPairing_source,
              ← twoMonogonPreHomeomorph_boundaryPairing_target]
            simp only [Homeomorph.symm_apply_apply]
            exact PolygonGluing.related_of_mem
              twoMonogonBoundaryPairing.identification
              twoMonogonBoundaryPairing_mem t
          · rw [← twoMonogonPreHomeomorph_reverseBoundaryPairing_source,
              ← twoMonogonPreHomeomorph_reverseBoundaryPairing_target]
            simp only [Homeomorph.symm_apply_apply]
            exact PolygonGluing.related_of_mem
              twoMonogonReverseBoundaryPairing.identification
              twoMonogonReverseBoundaryPairing_mem t
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The face relabeling identifies the generated finite-cyclic and typed sphere relations
exactly.
@isnad1 id=iff.0h2v.s8.9c9b12808967 from=translated src=- shape=15b1d93e vocab=8e96b272
-/
theorem twoMonogonPreHomeomorph_related_iff
    (x y : twoMonogonSphere.PolygonalPreRealization) :
    twoMonogonSphere.PolygonalGluingRel
        twoMonogonSphere_isSurfaceValid x y ↔
      SurfaceCellComplex.sphere.PolygonalGluingRel
        SurfaceCellComplex.sphere_occurrencePairingValid
        (twoMonogonPreHomeomorph x) (twoMonogonPreHomeomorph y) := by
  constructor
  · exact twoMonogonPreHomeomorph_related
  · intro hxy
    have hback := twoMonogonPreHomeomorph_symm_related hxy
    simpa only [Homeomorph.symm_apply_apply] using hback

/-- The faithful finite-cyclic two-monogon quotient is homeomorphic to the typed sphere
quotient. -/
noncomputable def twoMonogonRealizationHomeomorph :
    twoMonogonSphere.PolygonalRealization
        twoMonogonSphere_isSurfaceValid ≃ₜ
      SurfaceCellComplex.sphere.PolygonalRealization
        SurfaceCellComplex.sphere_occurrencePairingValid :=
  PolygonGluing.realizationCongr twoMonogonPreHomeomorph
    twoMonogonPreHomeomorph_related_iff

/-- The canonical finite-cyclic sphere presentation realizes the exact Eval sphere
representative. -/
noncomputable def twoMonogonSphereRepresentativeHomeomorph :
    twoMonogonSphere.PolygonalRealization
        twoMonogonSphere_isSurfaceValid ≃ₜ SphereRepresentative :=
  twoMonogonRealizationHomeomorph.trans
    SurfaceCellComplex.spherePolygonalRealizationHomeomorph

end FiniteCyclicPresentation

namespace NormalForm

/-- The sphere branch of `canonicalPresentation` realizes the exact Eval sphere
representative. -/
noncomputable def canonicalSphereRealizationHomeomorph :
    (canonicalPresentation .sphere).PolygonalRealization
        (canonicalPresentation_isSurfaceValid .sphere trivial) ≃ₜ
      SphereRepresentative :=
  FiniteCyclicPresentation.twoMonogonSphereRepresentativeHomeomorph

end NormalForm

end LeanEval.Topology.ClassificationOfSurfaces
