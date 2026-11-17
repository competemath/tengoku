import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

universe u
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

/--
@isnad1 id=isintegr.0h3v.s5.398f4612a91e from=translated src=- shape=216d8d42 vocab=6bc1229b
-/
theorem AlgebraicCurve.TwoChartIntegralModel.isIntegral
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j) := by exact @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.solution R _ F _ _ j _
