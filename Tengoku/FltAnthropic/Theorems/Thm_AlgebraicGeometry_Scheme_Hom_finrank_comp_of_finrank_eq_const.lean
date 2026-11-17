import Tengoku.Seed.AlgebraicGeometry.Morphisms.FlatRank
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=eq.1h7v.s6.0c59e158108c from=translated src=- shape=5b1b1db2 vocab=a8efba0b
-/
theorem AlgebraicGeometry.Scheme.Hom.finrank_comp_of_finrank_eq_const
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f] [IsFinite g] [Flat g]
    (m : ℕ) (hf : ∀ y : Y, f.finrank y = m) (z : Z) :
    (f ≫ g).finrank z = m * g.finrank z := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const.solution X Y Z f g _ _ _ _ m hf z
