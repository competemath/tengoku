import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FlatRank
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=isiso.2h6v.s6.e6290b912b00 from=translated src=- shape=e21a3b4c vocab=31756e08
-/
theorem AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ S) (f : X ⟶ S) (w : i ≫ g = f)
    [IsClosedImmersion i] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : ↥S, f.finrank s = g.finrank s) :
    IsIso i := by exact @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq.solution X Y S i g f w _ _ _ _ _ _ h
