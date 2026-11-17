import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=existsun.2h8v.s8.c4c687febcc1 from=translated src=- shape=353d688f vocab=6b61854e
-/
theorem AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_denseRange_of_comp_eq
    {W X Y Z : Scheme.{u}} [IsReduced X] (g : W ⟶ X) (hg : DenseRange g.base)
    (ι : Z ⟶ Y) [IsClosedImmersion ι] (φ : X ⟶ Y)
    (ψ : W ⟶ Z) (hψ : ψ ≫ ι = g ≫ φ) :
    ∃! χ : X ⟶ Z, χ ≫ ι = φ := by exact @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq.solution W X Y Z _ g hg ι _ φ ψ hψ
