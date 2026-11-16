import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=ex.2h7v.s7.05a098ad5c2f from=translated src=- shape=f4b63e91 vocab=2ad80825
-/
theorem solution
    {T T' A Z : Scheme.{0}} (π : T' ⟶ T) (hπ : π.ker = ⊥) (y : T ⟶ A) (ι : Z ⟶ A) [IsClosedImmersion ι]
    (h : ∃ z' : T' ⟶ Z, z' ≫ ι = π ≫ y) :
    ∃ z : T ⟶ Z, z ≫ ι = y := by
  obtain ⟨z', hz'⟩ := h
  have hle : ι.ker ≤ y.ker := by
    calc ι.ker ≤ (z' ≫ ι).ker := Scheme.Hom.le_ker_comp z' ι
      _ = (π ≫ y).ker := by rw [hz']
      _ = (π.ker).map y := Scheme.Hom.ker_comp π y
      _ = y.ker := by rw [hπ, Scheme.IdealSheafData.map_bot]
  exact ⟨IsClosedImmersion.lift ι y hle, IsClosedImmersion.lift_fac ι y hle⟩
