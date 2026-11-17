import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ChartPresentation

theorem isAffineOpen_V
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (C : Type u) [CommRing C] [Algebra R C] (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    {A : Type u} [CommRing A] (φ : R →+* A) :
    IsAffineOpen ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) := by
  letI : Algebra R A := φ.toAlgebra
  haveI : IsAffine (pullback (Spec.map (CommRingCat.ofHom (algebraMap R C))) (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :=
    IsAffine.of_isIso (pullbackSpecIso R C A).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl
  haveI : IsAffine (pullback (ι ≫ f) (Spec.map (CommRingCat.ofHom φ))) :=
    IsAffine.of_isIso (pullback.congrHom hι hφ).hom
  haveI : IsAffine (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) :=
    IsAffine.of_isIso (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom φ)) ι).hom
  have h := isAffineOpen_opensRange (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ))))
  rwa [Scheme.Hom.opensRange_pullbackSnd, ← Scheme.Hom.image_top_eq_opensRange] at h

end ChartPresentation
