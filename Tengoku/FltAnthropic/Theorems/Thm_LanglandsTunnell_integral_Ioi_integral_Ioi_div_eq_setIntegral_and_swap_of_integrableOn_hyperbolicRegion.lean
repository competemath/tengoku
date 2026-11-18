import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion
    (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ)
    (hf : IntegrableOn f {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}) :
    (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q ∧
      (∫ w in Ioi (0 : ℝ), ∫ σ in Ioi (v / w), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q := by exact @_root_.P2MW.S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion.solution v hv f hf
