import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_chartAlgFin_inf_chartAlgInf_eq_integralClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_chartAlgFin_inf_chartAlgInf_eq_integralClosure.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.chartAlgFin_inf_chartAlgInf_eq_integralClosure
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    (chartAlgFin R F j) ⊓ (chartAlgInf R F j) = integralClosure R F := by exact @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_chartAlgFin_inf_chartAlgInf_eq_integralClosure.solution R _ F _ _ j _
