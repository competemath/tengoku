import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian

set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory

universe u

theorem solution
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : X ⟶ Y) (w : h ≫ g = f)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation h := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : LocallyOfFiniteType (h ≫ g) := by rw [w]; infer_instance
  haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h g
  infer_instance
