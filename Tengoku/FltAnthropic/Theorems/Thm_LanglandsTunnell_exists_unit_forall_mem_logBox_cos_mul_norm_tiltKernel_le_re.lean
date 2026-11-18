import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Log
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

/--
@isnad1 id=ex.2h6v.s9.d8527ffa0557 from=translated src=- shape=1d66ebcc vocab=ab285444
-/
theorem LanglandsTunnell.exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re
    (S A B : ℂ) (δ ℓw ℓr : ℝ) (hδ : 0 ≤ δ)
    (hΔ : ((abs A.im) + (abs B.im)) * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr))) ≤ Real.pi) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ (w r M : ℝ), 0 ≤ M →
      w ∈ Icc (Real.exp (ℓw - δ)) (Real.exp (ℓw + δ)) → r ∈ Icc (Real.exp (ℓr - δ)) (Real.exp (ℓr + δ)) →
      Real.cos (((abs A.im) + (abs B.im)) * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr)))) *
          ‖((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-S) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B * (M : ℂ)‖
        ≤ (u * (((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-S) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B * (M : ℂ))).re := by exact @_root_.P2MW.S_LanglandsTunnell_exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re.solution S A B δ ℓw ℓr hδ hΔ
