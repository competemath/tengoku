import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=isiso.2h6v.s6.76e96c06e6da from=translated src=- shape=0342a028 vocab=31756e08
-/
theorem solution
    {X Y Z : Scheme.{u}} (fX : X ⟶ Z) (fY : Y ⟶ Z) (i : X ⟶ Y) (hi : i ≫ fY = fX)
    [IsClosedImmersion i]
    [IsFinite fX] [Flat fX] [LocallyOfFinitePresentation fX]
    [IsFinite fY] [Flat fY] [LocallyOfFinitePresentation fY]
    (hrank : ∀ z : Z, fX.finrank z = fY.finrank z) :
    IsIso i := by
  exact AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq i fY fX hi hrank
