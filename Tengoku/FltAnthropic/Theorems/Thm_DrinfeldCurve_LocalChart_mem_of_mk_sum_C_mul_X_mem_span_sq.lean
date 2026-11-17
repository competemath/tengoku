import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_LocalChart
import Tengoku.FltAnthropic.P2M.Sol.S_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=mem.3h9v.s14.840761b36c90 from=translated src=- shape=cccabe2d vocab=b60fec46
-/
theorem DrinfeldCurve.LocalChart.mem_of_mk_sum_C_mul_X_mem_span_sq
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] (I : Ideal W)
    (t : W) (ht : t ∈ I) (f u v : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (a : Fin 2 → W)
    (h : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u})
        (∑ ii : Fin 2, MvPowerSeries.C (a ii) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 1)}) ^ 2) :
    ∀ ii : Fin 2, a ii ∈ I := by exact @_root_.P2MW.S_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq.solution q _ W _ I t ht f u v hf a h
