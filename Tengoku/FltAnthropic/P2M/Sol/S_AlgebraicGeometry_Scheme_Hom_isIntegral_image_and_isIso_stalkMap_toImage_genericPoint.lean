import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

/--
@isnad1 id=ex.0h3v.s9.9f665390696c from=translated src=- shape=cdeefc61 vocab=45cd0533
-/
theorem solution
    {X P : Scheme.{u}} [IsIntegral X] (f : X ⟶ P) [IsImmersion f] [QuasiCompact f] :
    ∃ (_ : IsIntegral f.image),
      f.toImage.base (genericPoint X) = genericPoint f.image ∧
      IsIso (f.toImage.stalkMap (genericPoint X)) := by
  have hirr : IrreducibleSpace ↥f.image := by
    rw [irreducibleSpace_def]
    have h1 : IsIrreducible (Set.range ⇑f.toImage) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
    have h2 := h1.closure
    rwa [f.toImage.denseRange.closure_range] at h2
  have hcov : ∀ U : P.affineOpens, IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    have hq : _root_.IsReduced (Γ(P, (U : P.Opens)) ⧸ f.ker.ideal U) := by
      haveI : _root_.IsReduced (Γ(P, (U : P.Opens)) ⧸ RingHom.ker (f.app U).hom) :=
        isReduced_of_injective (RingHom.kerLift (f.app U).hom) (RingHom.kerLift_injective _)
      exact isReduced_of_injective (Ideal.quotEquivOfEq (f.ker_apply U))
        (Ideal.quotEquivOfEq (f.ker_apply U)).injective
    show IsReduced (Spec (.of (Γ(P, (U : P.Opens)) ⧸ f.ker.ideal U)))
    infer_instance
  have hred : IsReduced f.image :=
    @IsReduced.of_openCover f.image f.ker.subschemeCover.openCover hcov
  haveI : IsIntegral f.image := isIntegral_of_irreducibleSpace_of_isReduced f.image
  exact ⟨this, genericPoint_eq_of_isOpenImmersion f.toImage, inferInstance⟩
