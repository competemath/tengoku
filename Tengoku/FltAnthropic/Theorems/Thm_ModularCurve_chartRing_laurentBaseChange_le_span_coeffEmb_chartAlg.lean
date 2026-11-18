import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Definitions.Def_JacJ1_ChartAlgebra
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

open ModularCurve AlgebraicCurve
open scoped TensorProduct

/--
@isnad1 id=and.1h4v.s18.e0736efa536f from=translated src=- shape=a364649e vocab=525edc1d
-/
theorem ModularCurve.chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) (j : ↥F₀) [Fact (j ≠ 0)]
    (jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ)) :
    (AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ∧
    (AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) := by exact @_root_.P2MW.S_ModularCurve_chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg.solution F₀ p j _ jb hjb
