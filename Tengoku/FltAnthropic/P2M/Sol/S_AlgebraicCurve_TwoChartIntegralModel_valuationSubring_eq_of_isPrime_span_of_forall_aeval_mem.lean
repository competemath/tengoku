import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_valuationSubring_eq_of_isPrime_span_of_forall_aeval_mem.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_valuationSubring_eq_of_isPrime_span_of_forall_aeval_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u

open _root_.AlgebraicCurve.TwoChartIntegralModel open _root_.Polynomial

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (TwoChartIntegralModel TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf TwoChartIntegralModel.isIntegrallyClosed_chartAlg TwoChartIntegralModel.isFractionRing_chartAlg)
namespace TwoChartIntegralModel
export _root_.AlgebraicCurve.TwoChartIntegralModel (mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin fibre finiteType_chartAlgFin_and_chartAlgInf isIntegrallyClosed_chartAlg isFractionRing_chartAlg)
namespace VUAux
open _root_.AlgebraicCurve.TwoChartIntegralModel open _root_.AlgebraicCurve

variable {R : Type u} [CommRing R] [IsDomain R]

/--
@isnad1 id=eq.1h4v.s8.9cb73c6d96b8 from=translated src=- shape=3a8b746b vocab=d9e500ce
-/
theorem ofPrime_congr {K : Type u} [Field K] (A : ValuationSubring K) {P Q : Ideal ↥A}
    [P.IsPrime] [Q.IsPrime] (h : P = Q) : A.ofPrime P = A.ofPrime Q := by
  subst h; rfl

end AlgebraicCurve.TwoChartIntegralModel.VUAux

end
