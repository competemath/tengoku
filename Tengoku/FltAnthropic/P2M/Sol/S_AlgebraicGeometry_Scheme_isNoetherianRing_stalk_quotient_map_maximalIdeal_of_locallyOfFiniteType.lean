import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace FibreNoethAux

/--
@isnad1 id=isnoethe.0h2v.s5.9018b06b46e1 from=translated src=- shape=f82cba46 vocab=9e532e01
-/
theorem isNoetherianRing_of_essFiniteType (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  have h : IsNoetherianRing (Algebra.EssFiniteType.subalgebra R S) :=
    Algebra.FiniteType.isNoetherianRing R _
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) S h

/--
@isnad1 id=essfinit.0h2v.s5.03f239912073 from=translated src=- shape=ddb0a872 vocab=f43715be
-/
theorem essFiniteType_toStalk (A : Type) [CommRing A] (p : PrimeSpectrum A) :
    (StructureSheaf.toStalk A p).hom.EssFiniteType := by
  change (algebraMap A ((Spec.structureSheaf A).presheaf.stalk p)).EssFiniteType
  rw [RingHom.essFiniteType_algebraMap]
  exact Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl

/--
@isnad1 id=eq.0h4v.s13.f357fd002dc9 from=translated src=- shape=2ba761e0 vocab=22d4aa50
-/
theorem const_eq_comp (A : Type) [CommRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (x : X) :
    (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
      (f.stalkMap x).hom.comp (StructureSheaf.toStalk A (f.base x)).hom := by
  have h1 : (Spec (CommRingCat.of A)).presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x =
      f.appTop ≫ X.presheaf.germ ⊤ x trivial :=
    Scheme.Hom.germ_stalkMap f ⊤ x trivial
  have h2 : (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom := by
    simp only [CommRingCat.hom_comp, RingHom.comp_assoc]
  rw [h2, ← h1]
  rfl

/--
@isnad1 id=essfinit.0h4v.s12.0253506c3dcc from=translated src=- shape=53148626 vocab=222b4185
-/
theorem essFiniteType_const (A : Type) [CommRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f] (x : X) :
    ((X.presheaf.germ ⊤ x trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).EssFiniteType := by
  rw [const_eq_comp]
  exact RingHom.EssFiniteType.comp (essFiniteType_toStalk A (f.base x)) (LocallyOfFiniteType.stalkMap f x)

end FibreNoethAux

/--
@isnad1 id=isnoethe.1h4v.s13.4643a57009ff from=translated src=- shape=f4e733ad vocab=06d014a2
-/
theorem solution
    (A : Type) [CommRing A] [IsLocalRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f]
    (x : X) (hx : f.base x = closedPoint A) :
    IsNoetherianRing
      ((X.presheaf.stalk x) ⧸ Ideal.map
        ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
        (maximalIdeal A)) := by
  have hc := FibreNoethAux.essFiniteType_const A X f x
  letI alg : Algebra A (X.presheaf.stalk x) :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
  haveI hE : Algebra.EssFiniteType A (X.presheaf.stalk x) := hc
  have hq := Algebra.EssFiniteType.quotient_map (R := A) (S := X.presheaf.stalk x) (maximalIdeal A)
  letI fld : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  haveI : IsNoetherianRing (A ⧸ maximalIdeal A) := inferInstance
  have hN := @FibreNoethAux.isNoetherianRing_of_essFiniteType (A ⧸ maximalIdeal A)
    ((X.presheaf.stalk x) ⧸ (maximalIdeal A).map (algebraMap A (X.presheaf.stalk x))) _ _ _ hq inferInstance
  exact hN
