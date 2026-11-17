import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

/--
@isnad1 id=isiso.2h5v.s9.daf812bf65f0 from=translated src=- shape=ca1c5634 vocab=5c3e15dd
-/
theorem solution
    {P P' : Scheme.{u}} (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P') [IsOpenImmersion s]
    (hsβ : s ≫ β = U.ι) (hsr : Set.range s.base = β.base ⁻¹' (U : Set P)) :
    IsIso (β ∣_ U) := by
  have hr : Set.range s.base = Set.range (β ⁻¹ᵁ U).ι.base := by
    rw [hsr, Scheme.Opens.range_ι]; rfl
  let e := IsOpenImmersion.isoOfRangeEq s (β ⁻¹ᵁ U).ι hr
  have he : e.hom ≫ (β ⁻¹ᵁ U).ι = s := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h1 : e.hom ≫ (β ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, he, hsβ,
      Category.id_comp]
  have h2 : β ∣_ U = e.inv := by
    rw [← Category.id_comp (β ∣_ U), ← e.inv_hom_id, Category.assoc, h1, Category.comp_id]
  rw [h2]
  infer_instance
