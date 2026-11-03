/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.GenerationTime
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.Rouquier
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.Generators.Functor
import Tengoku.Seed.CategoryTheory.Triangulated.Adjunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generation invariants under triangulated functors

## Main results

* `CategoryTheory.ObjectProperty.generationTime_map_le` compares generation times of image
  properties.
* `CategoryTheory.ObjectProperty.generationTime_map_eq_of_equiv` states generation-time
  invariance under a triangulated equivalence.
* `CategoryTheory.Triangulated.rouquierDim_le_of_retract_coverage` proves dimension monotonicity
  when every target object is a retract of a functor image.
* `CategoryTheory.Triangulated.rouquierDim_le_of_essSurj` specializes that bound to essentially
  surjective functors.
* `CategoryTheory.Triangulated.rouquierDim_eq_of_equiv` states Rouquier-dimension invariance
  under a triangulated equivalence.

## Implementation notes

These results use the forward envelope transport in
`CategoryTheory.ObjectProperty.triangEnvelopeIter_map_le`. Rouquier dimension is indexed by
single objects, so target-wide results require retract coverage of the target; essential
surjectivity supplies this premise. Equivalence results use Mathlib's construction of a
triangulated quasi-inverse: its shift compatibility and exactness follow from the adjunction
associated to the equivalence.

## References

* Raphaël Rouquier, *Dimensions of triangulated categories*.
* `Mathlib.CategoryTheory.Triangulated.Generators` for the envelope tower.

## Tags

generation time, Rouquier dimension, triangulated category, exact functor
-/

universe v u v' u'

namespace CategoryTheory.ObjectProperty

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- Generation time does not increase after applying a triangulated functor to both properties.
No essential-surjectivity hypothesis is needed because the target property is the essential image
of the source property.
@isnad1 id=le.0h5v.s7.61f54f5304ff from=translated src=- shape=7ba8c9fd vocab=b86a7cc5
-/
theorem generationTime_map_le (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (P Q : ObjectProperty C) :
    (P.map F).generationTime (Q.map F) ≤ P.generationTime Q := by
  apply sInf_le_sInf
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨n, (map_monotone hn F).trans (triangEnvelopeIter_map_le F P n), rfl⟩

private lemma triangEnvelopeIter_isoClosure (P : ObjectProperty C) (n : ℕ) :
    P.isoClosure.triangEnvelopeIter n = P.triangEnvelopeIter n := by
  have hs : P.isoClosure.shiftClosure ℤ = P.shiftClosure ℤ := by
    apply le_antisymm
    · exact (shiftClosure_le_iff _ _).2 ((isoClosure_le_iff _ _).2 P.le_shiftClosure)
    · exact monotone_shiftClosure P.le_isoClosure
  simp only [triangEnvelopeIter, hs]

/-- Generation time is invariant under a triangulated equivalence. The image properties are
essential images under `E.functor`; because envelope stages are invariant under isomorphism, they
have the same generation time as their source properties. The triangulated structure on the
quasi-inverse is supplied by Mathlib's equivalence adjunction.
@isnad1 id=eq.0h5v.s7.a92f11e9ed02 from=translated src=- shape=2961ad33 vocab=b26db530
-/
theorem generationTime_map_eq_of_equiv (E : C ≌ D) [E.functor.CommShift ℤ]
    [E.functor.IsTriangulated] (P Q : ObjectProperty C) :
    (P.map E.functor).generationTime (Q.map E.functor) = P.generationTime Q := by
  apply le_antisymm (generationTime_map_le E.functor P Q)
  letI := E.commShiftInverse ℤ
  letI := E.commShift_of_functor ℤ
  letI := E.toAdjunction.isTriangulated_rightAdjoint
  apply le_sInf
  rintro _ ⟨n, hn, rfl⟩
  apply (generationTime_le_coe_iff P Q n).2
  intro X hX
  have hmap : ∀ Y, P.map E.functor Y → P.isoClosure (E.inverse.obj Y) := by
    rintro Y ⟨Z, hZ, ⟨e⟩⟩
    exact ⟨Z, hZ, ⟨(E.inverse.mapIso e).symm.trans (E.unitIso.app Z).symm⟩⟩
  have h := triangEnvelopeIter_map_obj_of_le E.inverse _ _ hmap (E.functor.obj X) n
    (hn _ (Q.prop_map_obj E.functor hX))
  rw [triangEnvelopeIter_isoClosure] at h
  exact (P.triangEnvelopeIter n).prop_of_iso (E.unitIso.app X).symm h

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- Rouquier dimension is monotone under a triangulated functor whose image is retract-dense:
every target object is a retract of some image.
@isnad1 id=le.1h3v.s7.cb9d1ccc217a from=translated src=- shape=10dae46a vocab=40e8193d
-/
theorem rouquierDim_le_of_retract_coverage (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hCover : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    rouquierDim D ≤ rouquierDim C := by
  unfold rouquierDim
  refine le_iInf fun G => le_sInf ?_
  rintro _ ⟨n, hn, rfl⟩
  apply (rouquierDim_le_coe_iff D n).2
  refine ⟨F.obj G,
    singleton_triangEnvelopeIter_top_of_retract_coverage F hCover G n (top_le_iff.mp hn)⟩

/-- Rouquier dimension cannot increase under an essentially-surjective triangulated functor.
Essential surjectivity supplies the retract-coverage premise of
`CategoryTheory.Triangulated.rouquierDim_le_of_retract_coverage`.
@isnad1 id=le.0h3v.s7.c04042a6ab78 from=translated src=- shape=bd850565 vocab=33b25599
-/
theorem rouquierDim_le_of_essSurj (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F.EssSurj] :
    rouquierDim D ≤ rouquierDim C := by
  apply rouquierDim_le_of_retract_coverage F
  intro Y
  let X := F.objPreimage Y
  exact ⟨X, ⟨(F.objObjPreimageIso Y).symm.retract⟩⟩

/-- A triangulated equivalence preserves Rouquier dimension. Mathlib supplies the compatible
shift structure and triangulated structure on the quasi-inverse from the equivalence adjunction.
@isnad1 id=eq.0h3v.s7.f0f2f5d6bf8d from=translated src=- shape=183380f4 vocab=19a7cec5
-/
theorem rouquierDim_eq_of_equiv (E : C ≌ D) [E.functor.CommShift ℤ]
    [E.functor.IsTriangulated] : rouquierDim C = rouquierDim D := by
  letI := E.commShiftInverse ℤ
  letI := E.commShift_of_functor ℤ
  letI := E.toAdjunction.isTriangulated_rightAdjoint
  exact le_antisymm (rouquierDim_le_of_essSurj E.inverse) (rouquierDim_le_of_essSurj E.functor)

end CategoryTheory.Triangulated
