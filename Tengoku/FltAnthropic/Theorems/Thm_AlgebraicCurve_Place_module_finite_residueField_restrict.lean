import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorPushPull
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_module_finite_residueField_restrict

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_module_finite_residueField_restrict.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve
theorem AlgebraicCurve.Place.module_finite_residueField_restrict (K F F' : Type*)
    [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] (w : Place K F') :
    Module.Finite (w.restrict F).ResidueField w.ResidueField := by exact @_root_.P2MW.S_AlgebraicCurve_Place_module_finite_residueField_restrict.solution K F F' _ _ _ _ _ _ _ _ w
