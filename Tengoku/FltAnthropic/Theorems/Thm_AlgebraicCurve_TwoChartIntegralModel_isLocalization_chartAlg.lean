import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=islocali.0h5v.s10.4b45c052e707 from=translated src=- shape=23e2a461 vocab=7b25b416
-/
theorem AlgebraicCurve.TwoChartIntegralModel.isLocalization_chartAlg
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    (M : Submonoid R) [IsLocalization M R'] (S : Set F) :
    letI : Algebra (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S)
        (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F S) :=
      (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' S).toAlgebra
    IsLocalization (M.map (algebraMap R (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S)))
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F S) := by exact @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg.solution R _ F _ _ R' _ _ _ _ M _ S
