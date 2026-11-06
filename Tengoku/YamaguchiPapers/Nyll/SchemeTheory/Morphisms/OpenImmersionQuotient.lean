/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.QuotientBaseChange
public import Tengoku.Seed.Algebra.Category.Ring.Constructions
public import Tengoku.Seed.AlgebraicGeometry.OpenImmersion
public import Tengoku.Seed.AlgebraicGeometry.Pullbacks
public import Tengoku.Seed.CategoryTheory.MorphismProperty.Limits
public import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
public import Tengoku.Seed.RingTheory.TensorProduct.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Open immersions after quotient base change

The literal map `R / I → S / I S` is the base change of a ring map `R → S`.
Its pushout square is obtained from the tensor-product pushout and the
canonical quotient/tensor-product equivalence. Consequently its spectrum
is an open immersion whenever the original spectrum map is.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace CommRingCat

/-- Extension of an ideal gives the canonical pushout square of quotient
ring maps.
@isnad1 id=ispushou.0h4v.s9.2f2528df050b from=translated src=- shape=b3d28b6e vocab=a2e1ed78
-/
theorem isPushout_quotientMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) :
    IsPushout (ofHom f) (ofHom (Ideal.Quotient.mk I))
      (ofHom (Ideal.Quotient.mk (I.map f)))
      (ofHom (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) := by
  let : Algebra R S := f.toAlgebra
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toRingEquiv
  refine (isPushout_tensorProduct R S (R ⧸ I)).of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · ext s
    rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (1 : S) ⊗ₜ[R] (Ideal.Quotient.mk I r) =
      f r ⊗ₜ[R] (1 : R ⧸ I)
    exact (Algebra.TensorProduct.includeRight : (R ⧸ I) →ₐ[R]
      S ⊗[R] (R ⧸ I)).commutes r

end CommRingCat

namespace AlgebraicGeometry

/-- The canonical quotient square becomes a pullback square on spectra.
@isnad1 id=ispullba.0h4v.s9.1972540037ba from=translated src=- shape=c0258b58 vocab=59c48361
-/
theorem isPullback_SpecMap_quotientMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))))
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)))
      (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_quotientMap f I)

/-- Open immersions remain open immersions under the literal quotient map.
@isnad1 id=isopenim.0h4v.s9.7518763e61da from=translated src=- shape=5c417a3a vocab=67569906
-/
theorem isOpenImmersion_SpecMap_quotientMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_SpecMap_quotientMap f I) inferInstance

/-- The same result with the extended ideal written using a chosen equal ideal.
@isnad1 id=isopenim.1h5v.s8.49e6b3458205 from=translated src=- shape=7d443f2c vocab=2c4bf3b2
-/
theorem isOpenImmersion_SpecMap_quotientMap_of_map_eq
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (hJ : I.map f = J)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap J f (hJ ▸ Ideal.le_comap_map)))) := by
  subst J
  exact isOpenImmersion_SpecMap_quotientMap f I

/-- Reduction by an ideal in a common scalar ring preserves an open immersion
for the canonical quotient-base algebra map.
@isnad1 id=isopenim.0h5v.s10.db7ab427f29f from=translated src=- shape=6d18160d vocab=bfc56e21
-/
theorem isOpenImmersion_SpecMap_quotientBaseChange
    {R : Type v} {A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (I : Ideal R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (f.quotientBaseChange I).toRingHom)) :=
  isOpenImmersion_SpecMap_quotientMap_of_map_eq f.toRingHom
    (I.map (algebraMap R A)) (I.map (algebraMap R B)) (f.map_extendedIdeal I)

end AlgebraicGeometry
