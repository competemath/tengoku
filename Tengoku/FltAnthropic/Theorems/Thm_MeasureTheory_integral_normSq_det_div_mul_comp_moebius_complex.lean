import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Complex
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ z : ℂ, ((‖a * d - b * c‖ ^ 2 / ‖a + z * c‖ ^ 4 : ℝ) : ℂ) * G ((b + z * d) / (a + z * c))
      = ∫ u : ℂ, G u := by exact @_root_.P2MW.S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex.solution a b c d _hdet G
