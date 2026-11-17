import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (G : ℝ → ℂ) :
    ∫ x : ℝ, ((|a * d - b * c| / (a + x * c) ^ 2 : ℝ) : ℂ) * G ((b + x * d) / (a + x * c))
      = ∫ u : ℝ, G u := by exact @_root_.P2MW.S_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real.solution a b c d _hdet G
