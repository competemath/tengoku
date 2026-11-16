import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    IsRegularLocalRing (X.presheaf.stalk (i.base u)) ↔ IsRegularLocalRing (U.presheaf.stalk u) := by
  let e : X.presheaf.stalk (i.base u) ≃+* U.presheaf.stalk u := (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e, fun h => IsRegularLocalRing.of_ringEquiv e.symm⟩
