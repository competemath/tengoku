module
public import Tengoku.Seed.RingTheory.Localization.LocalizationLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.LocalizationInStagesAtPrime

universe u v

/-- If `L` is a localization of `B`, the local rings over compatible residue
kernels are canonically equivalent. The center equality is derived from the
commuting residue maps; no height or DVR hypothesis is used.
@isnad1 id=ex.2h6v.s12.331a58094ceb from=translated src=- shape=ba62e711 vocab=ce95039f
-/
theorem kernel_center_localization_equiv
    {B : Type u} [CommRing B] {κ : Type v} [Field κ]
    (M : Submonoid B)
    (p : Ideal (Localization M)) [p.IsPrime]
    (rhoL : Localization M →+* κ) (rhoB : B →+* κ)
    (hp : p = RingHom.ker rhoL)
    (hLoc : rhoL.comp (algebraMap B (Localization M)) = rhoB) :
    ∃ e : Localization.AtPrime p ≃ₐ[B]
        Localization.AtPrime (p.comap (algebraMap B (Localization M))),
      p.comap (algebraMap B (Localization M)) = RingHom.ker rhoB ∧
      ∀ b : B,
        e (algebraMap (Localization M) (Localization.AtPrime p)
          (algebraMap B (Localization M) b)) =
          algebraMap B
            (Localization.AtPrime (p.comap (algebraMap B (Localization M)))) b := by
  have hcenter : p.comap (algebraMap B (Localization M)) = RingHom.ker rhoB := by
    ext b
    rw [Ideal.mem_comap, hp, RingHom.mem_ker]
    change rhoL (algebraMap B (Localization M) b) = 0 ↔ rhoB b = 0
    have heq : rhoL (algebraMap B (Localization M) b) = rhoB b := by
      simpa only [RingHom.comp_apply] using
        congrArg (fun f : B →+* κ => f b) hLoc
    rw [heq]
  let e0 := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p
  have e : Localization.AtPrime p ≃ₐ[B]
      Localization.AtPrime (p.comap (algebraMap B (Localization M))) := e0.symm
  refine ⟨e, hcenter, ?_⟩
  intro b
  have htower :
      algebraMap (Localization M) (Localization.AtPrime p)
        (algebraMap B (Localization M) b) =
      algebraMap B (Localization.AtPrime p) b :=
    IsScalarTower.algebraMap_apply B (Localization M) (Localization.AtPrime p) b
  rw [htower]
  exact e.commutes b

end Stafford38.Geometry.LocalizationInStagesAtPrime
