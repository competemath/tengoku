import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=eq.0h2v.s9.e217a6e793b4 from=translated src=- shape=75129050 vocab=9f71e39b
-/
theorem Matrix.GeneralLinearGroup.modularCharacter_fin_two_eq_one
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] (g : GL (Fin 2) F) :
    MeasureTheory.Measure.modularCharacter g = 1 := by exact @_root_.P2MW.S_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one.solution F _ _ _ _ g
