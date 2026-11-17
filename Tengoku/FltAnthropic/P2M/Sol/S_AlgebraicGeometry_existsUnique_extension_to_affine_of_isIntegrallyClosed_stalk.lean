import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.TopologicalSpace open _root_.Opposite

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Hom.resLE_comp_ι IsLocallyNoetherian IsOpenImmersion.lift Surjective Scheme.Opens.range_ι Scheme.Hom Scheme.isoSpec_hom isInitialOfIsEmpty ext_of_isAffine IsAffine Spec IsIntegral Scheme ext_of_isDominant Scheme.Hom.appTop isReduced_of_isReduced_stalk Scheme.toSpecΓ_appTop IsOpenImmersion functionField_isFractionRing_of_isAffineOpen germ_injective_of_isIntegral Scheme.Hom.comp_appTop Scheme.openCoverOfIsOpenCover_f isIntegral_of_isOpenImmersion IsReduced IsLocallyNoetherian.component_noetherian exists_isAffineOpen_mem_and_subset isLocallyNoetherian_of_isOpenImmersion isAffineOpen_top ΓSpec.adjunction isIntegral_of_isAffine_of_isDomain Scheme.Cover.glueMorphisms Scheme.Opens.ι_apply ΓSpec_adjunction_homEquiv_eq IsDominant IsAffineOpen Scheme.Hom.preimage_iSup Scheme.Hom.resLE_comp_ι_assoc Scheme.Opens isDominant_iff Scheme.Cover.hom_ext Scheme.Opens.ι_app Scheme.Hom.comp_preimage IsOpenImmersion.lift_fac Scheme.Hom.comp_apply geometrically Scheme.Cover Scheme.ΓSpecIso)
namespace HartogsAffine
open _root_.AlgebraicGeometry

section Affine

variable {X : Scheme.{u}} [IsAffine X]

noncomputable def pointOfPrime (p : PrimeSpectrum Γ(X, ⊤)) : (⊤ : X.Opens) :=
  ⟨(isAffineOpen_top X).fromSpec.base p, trivial⟩

/--
@isnad1 id=eq.0h2v.s10.4be749474df5 from=translated src=- shape=daa79696 vocab=3dcf2460
-/
theorem primeIdealOf_pointOfPrime (p : PrimeSpectrum Γ(X, ⊤)) :
    (isAffineOpen_top X).primeIdealOf (pointOfPrime p) = p := by
  have h := (isAffineOpen_top X).fromSpec_primeIdealOf (pointOfPrime p)
  change (isAffineOpen_top X).fromSpec.base _ = (isAffineOpen_top X).fromSpec.base p at h
  exact (isAffineOpen_top X).fromSpec.isOpenEmbedding.injective h

/--
@isnad1 id=atprime.0h2v.s11.df3c069a1448 from=translated src=- shape=afd66ed9 vocab=0201ae30
-/
scoped instance isLocalization_stalk_pointOfPrime (p : PrimeSpectrum Γ(X, ⊤)) :
    IsLocalization.AtPrime (X.presheaf.stalk (pointOfPrime p).1) p.asIdeal := by
  have := (isAffineOpen_top X).isLocalization_stalk (pointOfPrime p)
  rwa [primeIdealOf_pointOfPrime] at this

/--
@isnad1 id=isintegr.1h1v.s10.8a62a07466fb from=translated src=- shape=218c9427 vocab=38d20ae3
-/
theorem isIntegrallyClosed_sections [IsDomain Γ(X, ⊤)]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : IsIntegrallyClosed Γ(X, ⊤) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  haveI := h (pointOfPrime ⟨p, hp.isPrime⟩).1
  haveI := isLocalization_stalk_pointOfPrime (X := X) ⟨p, hp.isPrime⟩
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (pointOfPrime ⟨p, hp.isPrime⟩).1)
      (Localization.AtPrime p)).toRingEquiv

end Affine

section Sections

variable {X : Scheme.{u}} [IsIntegral X]

variable [IsAffine X]

end Sections

section LocallyIntegral

end LocallyIntegral

section Wrapper

variable {T : Scheme.{u}} [IsLocallyNoetherian T]

end Wrapper

section Glue

variable {T : Scheme.{u}}

end Glue

section Main

end Main

end AlgebraicGeometry.HartogsAffine
open scoped _root_.P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine
open scoped _root_.P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry
