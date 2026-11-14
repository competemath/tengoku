import Tengoku.Aintlib.ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A basic-open criterion for quasicoherence

This file reconstructs quasicoherence on an affine spectrum from compatible
tensor-product descriptions of sections on basic opens.
-/
namespace Tengoku.Aintlib end Tengoku.Aintlib open Tengoku.Aintlib
open CategoryTheory Opposite TensorProduct TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- A module on `Spec R` is quasicoherent if its sections on every basic open
are obtained from global sections by extension of scalars, compatibly with
restriction on pure tensors.
@isnad1 id=isquasic.1h3v.s15.4ad2b9650624 from=translated src=- shape=66617ccc vocab=7be49514
-/
theorem isQuasicoherent_of_basicOpen_tensorEquiv
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (e : ∀ r : R,
      Γ(Spec R, specBasicOpen R r) ⊗[R] Γ(M, (⊤ : (Spec R).Opens)) ≃ₗ[
        Γ(Spec R, specBasicOpen R r)] Γ(M, specBasicOpen R r))
    (he : ∀ (r : R) (m : Γ(M, (⊤ : (Spec R).Opens))),
      e r ((1 : Γ(Spec R, specBasicOpen R r)) ⊗ₜ[R] m) =
        M.presheaf.map (specBasicOpen R r).leTop.op m) :
    M.IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ]
  rw [isIso_fromTildeΓ_iff_isLocalizing]
  intro r
  let A := Γ(Spec R, specBasicOpen R r)
  let localizationUnit : Γ(M, (⊤ : (Spec R).Opens)) →ₗ[R]
      A ⊗[R] Γ(M, (⊤ : (Spec R).Opens)) :=
    TensorProduct.mk R A Γ(M, (⊤ : (Spec R).Opens)) 1
  let er := (e r).restrictScalars R
  let target := er.toLinearMap.comp localizationUnit
  letI : IsLocalization.Away r A := inferInstance
  letI : IsLocalizedModule.Away r localizationUnit := inferInstance
  letI : IsLocalizedModule.Away r target :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers r) localizationUnit er
  have htarget : IsLocalizedModule.Away r target := inferInstance
  have htarget_eq : target =
      ((modulesSpecToSheaf.obj M).obj.map
        (specBasicOpen R r).leTop.op).hom := by
    ext m
    exact he r m
  rw [← htarget_eq]
  exact htarget

end

end AlgebraicGeometry.Scheme.Modules
-- Tengoku: root names of this library moved to Tengoku.Aintlib so they do not collide with other libraries (generated)
