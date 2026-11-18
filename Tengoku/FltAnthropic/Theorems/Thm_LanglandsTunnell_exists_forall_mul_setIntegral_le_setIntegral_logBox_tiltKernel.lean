import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Log
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

/--
@isnad1 id=ex.3h5v.s10.af301c90659d from=translated src=- shape=b0b00ade vocab=2db62337
-/
theorem LanglandsTunnell.exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel
    (a : ℝ) (ha : a ≠ 0) (α β : ℝ) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      (1 - η) * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ α * r ^ β * Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))
        ≤ ∫ w in Icc (Real.exp ((1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y / (Real.pi * |a|))))) / a ^ 2) - δ))
                   (Real.exp ((1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y / (Real.pi * |a|))))) / a ^ 2) + δ)),
          ∫ r in Icc (Real.exp (((1/3 : ℝ) * Real.log (y / (Real.pi * |a|)) -
                        (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y / (Real.pi * |a|))))) / a ^ 2)) - δ))
                     (Real.exp (((1/3 : ℝ) * Real.log (y / (Real.pi * |a|)) -
                        (1/4 : ℝ) * Real.log ((1 + Real.exp (2 * ((1/3 : ℝ) * Real.log (y / (Real.pi * |a|))))) / a ^ 2)) + δ)),
          (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ α * r ^ β * Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) := by exact @_root_.P2MW.S_LanglandsTunnell_exists_forall_mul_setIntegral_le_setIntegral_logBox_tiltKernel.solution a ha α β η δ hη hδ
