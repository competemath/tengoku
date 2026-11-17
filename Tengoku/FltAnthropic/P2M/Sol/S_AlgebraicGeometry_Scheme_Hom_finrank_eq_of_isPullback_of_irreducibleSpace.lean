import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_finrank_eq_of_isPullback_of_irreducibleSpace.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_eq_of_isPullback_of_irreducibleSpace

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=eq.2h10v.s7.b3d8ea9ea350 from=translated src=- shape=e259d68e vocab=1843b26e
-/
theorem solution
    {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] [IrreducibleSpace Y]
    (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (h : IsPullback g' π' π g) [Nonempty Y'] (d : ℕ)
    (hd : ∀ y' : Y', π'.finrank y' = d) (y : Y) : π.finrank y = d := by
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y')
  have hlc := Scheme.Hom.isLocallyConstant_finrank π
  have h1 : π.finrank (g y₀) = d := by
    rw [← Scheme.Hom.finrank_of_isPullback g' π' π g h y₀]
    exact hd y₀
  rw [← h1]
  exact hlc.apply_eq_of_preconnectedSpace y (g y₀)
