import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing
attribute [-simp] DrinfeldCurve.LocalChart.ChartPresentation.mk.sizeOf_spec DrinfeldCurve.LocalChart.ChartPresentation.mk.injEq

set_option autoImplicit false

/--
@isnad1 id=and.1h7v.s11.e6f4ba3969b6 from=translated src=- shape=47aed77d vocab=5266da17
-/
theorem MvPowerSeries.mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow
    (W : Type) [CommRing W] (G h : MvPowerSeries (Fin 2) W) (d k : ℕ)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d) (a b : W) :
    G * h ^ k ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (d * k) ∧
      (∑ i ∈ Finset.range (d * k + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) (G * h ^ k)
              * a ^ i * b ^ (d * k - i)) =
        MvPowerSeries.constantCoeff G *
          (∑ i ∈ Finset.range (d + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) h
              * a ^ i * b ^ (d - i)) ^ k := by exact @_root_.P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.solution W _ G h d k hh a b
