import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Log
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral
    (a : ℝ) (ha : a ≠ 0) (A B : ℂ) (τ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      (1 - ε) * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          ‖((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-((y : ℂ) + (τ : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)‖
        ≤ ‖∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          ((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-((y : ℂ) + (τ : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)‖ := by exact @_root_.P2MW.S_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral.solution a ha A B τ ε hε
