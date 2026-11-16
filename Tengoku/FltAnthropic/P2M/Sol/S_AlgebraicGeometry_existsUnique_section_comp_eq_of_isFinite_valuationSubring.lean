import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_valuationSubring.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_valuationSubring

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {L : Type u} [Field L] (O : ValuationSubring L)
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of ↥O)) [IsFinite f]
    (x : Spec (CommRingCat.of L) ⟶ Z) (hx : x ≫ f = Spec.map (CommRingCat.ofHom O.subtype)) :
    ∃! z : Spec (CommRingCat.of ↥O) ⟶ Z, z ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom O.subtype) ≫ z = x := by
  haveI : IsProper f := inferInstance
  haveI : UniversallyClosed f := inferInstance
  haveI : IsSeparated f := inferInstance
  exact AlgebraicGeometry.existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
    (R := ↥O) (K := L) f x hx
