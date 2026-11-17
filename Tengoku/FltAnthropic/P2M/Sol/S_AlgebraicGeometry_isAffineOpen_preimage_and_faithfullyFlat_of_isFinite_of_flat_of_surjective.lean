import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=and.2h4v.s13.c1c1500c6d20 from=translated src=- shape=ecc9f833 vocab=8004b736
-/
theorem solution
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [Flat g] (hsurj : Function.Surjective g)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (g ⁻¹ᵁ U) ∧ Function.Injective (g.app U).hom ∧
      (letI _i : Algebra Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra;
        Module.FaithfullyFlat Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) := by
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  letI _i : Algebra Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra

  have hflat : (g.app U).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @Flat g inferInstance ⟨U, hU⟩ ⟨g ⁻¹ᵁ U, hV⟩ le_rfl
  haveI : Module.Flat Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := hflat

  have hcomap : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, g ⁻¹ᵁ U))) := by
    intro q
    obtain ⟨x, hx⟩ := hsurj (hU.fromSpec q)
    have hxV : x ∈ g ⁻¹ᵁ U := by
      show g x ∈ U
      rw [hx]
      have : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
      rw [hU.range_fromSpec] at this
      exact this
    obtain ⟨p, hp⟩ : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
    refine ⟨p, hU.fromSpec.isOpenEmbedding.injective ?_⟩
    have h := IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at h
    have h' := congrArg (fun φ => φ p) h
    simp only [Scheme.Hom.comp_apply] at h'
    rw [hp, hx] at h'
    exact h'
  haveI hff : Module.FaithfullyFlat Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := Module.FaithfullyFlat.of_comap_surjective hcomap
  exact ⟨hV, FaithfulSMul.algebraMap_injective Γ(Y, U) Γ(X, g ⁻¹ᵁ U), hff⟩
