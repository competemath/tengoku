import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
import Tengoku.Seed.AlgebraicGeometry.Properties
import Tengoku.Seed.RingTheory.RingHom.LocallyStandardSmooth
import Tengoku.Seed.RingTheory.Unramified.Field
import Tengoku.Seed.RingTheory.Localization.Away.Basic
import Tengoku.Seed.RingTheory.Etale.Basic
import Tengoku.Seed.RingTheory.Smooth.Flat
import Tengoku.Seed.RingTheory.Flat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isReduced_of_smooth_over_field.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isReduced_of_smooth_over_field

set_option autoImplicit false

universe u

open TensorProduct

namespace IsReducedOfSmoothFieldAux

/--
@isnad1 id=isreduce.0h2v.s5.ef717c6c92cd from=translated src=- shape=962998db vocab=4c7e4ece
-/
theorem etale_isReduced (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Etale K A] : IsReduced A := by
  haveI : Algebra.FormallyUnramified K A := inferInstance
  haveI : Algebra.EssFiniteType K A := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K A

/--
@isnad1 id=isreduce.1h3v.s6.9d5ca306e1dd from=translated src=- shape=b29ca70b vocab=cd91e770
-/
theorem isStandardSmooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.IsStandardSmooth) : IsReduced A := by
  obtain ⟨n, g, -, hg⟩ := hφ.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin n) R) A := g.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) A := hg.toAlgebra
  haveI : IsReduced
      (FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A) :=
    IsReducedOfSmoothFieldAux.etale_isReduced (FractionRing (MvPolynomial (Fin n) R)) _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight :
      A →ₐ[MvPolynomial (Fin n) R]
        FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A)
    (Algebra.TensorProduct.includeRight_injective
      (IsFractionRing.injective (MvPolynomial (Fin n) R)
        (FractionRing (MvPolynomial (Fin n) R))))

/--
@isnad1 id=isreduce.1h3v.s6.74d8970281ca from=translated src=- shape=b29ca70b vocab=83af59b1
-/
theorem smooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.Smooth) : IsReduced A := by
  rw [RingHom.smooth_iff_locally_isStandardSmooth] at hφ
  obtain ⟨s, hs, H⟩ := hφ
  constructor
  intro x hx
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  rw [map_zero]
  funext a
  haveI : IsReduced (Localization.Away a.1) :=
    IsReducedOfSmoothFieldAux.isStandardSmooth_isReduced_of_isDomain (H a.1 a.2)
  simpa using IsReduced.eq_zero _ (hx.map (algebraMap A (Localization.Away a.1)))

end IsReducedOfSmoothFieldAux

section SchemeLevel

open AlgebraicGeometry CategoryTheory

/--
@isnad1 id=isreduce.1h3v.s5.268f1c8bfc0c from=translated src=- shape=6cb0ac8b vocab=62474dde
-/
theorem solution {k : Type u} [Field k]
    {Z : Scheme.{u}} {g : Z ⟶ Spec (.of k)} (hg : Smooth g) : IsReduced Z := by
  haveI := hg
  haveI : ∀ i, IsReduced (Z.affineCover.X i) := by
    intro i
    haveI : IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
      Function.Injective.isDomain _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
    haveI : _root_.IsReduced ↑Γ(Z.affineCover.X i, ⊤) :=
      IsReducedOfSmoothFieldAux.smooth_isReduced_of_isDomain
        ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp
          (inferInstance : Smooth (Z.affineCover.f i ≫ g)))
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ Z.affineCover

end SchemeLevel

