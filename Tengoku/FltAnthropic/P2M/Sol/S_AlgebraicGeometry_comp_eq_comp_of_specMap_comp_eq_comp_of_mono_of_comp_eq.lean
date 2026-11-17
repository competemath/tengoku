import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=eq.4h12v.s8.6769e1e1d7f9 from=translated src=- shape=32f5c2e6 vocab=1b0a936f
-/
theorem solution
    {A Q : Type u} [CommRing A] [CommRing Q] (π : A →+* Q)
    {Y K : Scheme.{u}} (ι : Spec (CommRingCat.of A) ⟶ Y) [Mono ι] (k₁ : K ⟶ Y)

    (pr : Spec (CommRingCat.of Q) ⟶ K)
    (hpr : Spec.map (CommRingCat.ofHom π) ≫ ι = pr ≫ k₁)

    (E₁ E₂ : Y ⟶ Y) (f₁ f₂ : A →+* A)
    (hf₁ : Spec.map (CommRingCat.ofHom f₁) ≫ ι = ι ≫ E₁)
    (hf₂ : Spec.map (CommRingCat.ofHom f₂) ≫ ι = ι ≫ E₂)

    (hK : k₁ ≫ E₁ = k₁ ≫ E₂) :
    π.comp f₁ = π.comp f₂ := by
  have hspec : Spec.map (CommRingCat.ofHom (π.comp f₁)) = Spec.map (CommRingCat.ofHom (π.comp f₂)) := by
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
    apply (cancel_mono ι).mp
    rw [Category.assoc, Category.assoc, hf₁, hf₂, ← Category.assoc, ← Category.assoc, hpr, Category.assoc, Category.assoc, hK]
  have hinj := Spec.map_injective hspec
  have := congrArg CommRingCat.Hom.hom hinj
  simpa only [CommRingCat.hom_ofHom] using this
