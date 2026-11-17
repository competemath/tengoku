import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isReduced_of_flat_of_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [IsReduced X] : IsReduced Y := by
  haveI : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    let φ := (f.stalkMap x).hom
    letI := φ.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom φ)
    haveI : Module.FaithfullyFlat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isReduced_of_injective (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x))
      (FaithfulSMul.algebraMap_injective _ _)
  exact isReduced_of_isReduced_stalk Y
