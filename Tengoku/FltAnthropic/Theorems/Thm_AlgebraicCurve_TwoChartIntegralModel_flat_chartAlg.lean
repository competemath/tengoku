import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=flat.1h3v.s8.7ffc6a6ba351 from=translated src=- shape=27f57e3d vocab=512c42b7
-/
theorem AlgebraicCurve.TwoChartIntegralModel.flat_chartAlg
    {R F : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field F] [Algebra R F]
    (hRF : Function.Injective (algebraMap R F)) (S : Set F) :
    Module.Flat R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S) := by exact @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg.solution R F _ _ _ _ _ hRF S
