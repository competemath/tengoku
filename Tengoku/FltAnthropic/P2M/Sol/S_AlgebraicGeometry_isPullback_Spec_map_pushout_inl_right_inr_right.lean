import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isPullback_Spec_map_pushout_inl_right_inr_right.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isPullback_Spec_map_pushout_inl_right_inr_right

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=ispullba.0h6v.s8.90edbf0635ab from=translated src=- shape=186bcb23 vocab=819eface
-/
theorem solution
    {R : Type u} [CommRing R] {B B₁ B₂ : Under (CommRingCat.of R)} (φ₁ : B ⟶ B₁) (φ₂ : B ⟶ B₂) :
    IsPullback (Spec.map (pushout.inl φ₁ φ₂).right) (Spec.map (pushout.inr φ₁ φ₂).right)
      (Spec.map φ₁.right) (Spec.map φ₂.right) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ ((IsPushout.of_hasPushout φ₁ φ₂).map (Under.forget _))
