import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=bijectiv.1h5v.s11.c6fcac9cb81b from=translated src=- shape=96e4f5d4 vocab=970764a0
-/
theorem AlgebraicGeometry.Scheme.Modules.bijective_unit_app_of_le_opensRange
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (N : X.Modules)
    (V : X.Opens) (hV : V ≤ j.opensRange) :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app V) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange.solution X Y j _ N V hV
