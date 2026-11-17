import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Filter Topology

/--
@isnad1 id=tendsto.1h3v.s8.4956603621ab from=translated src=- shape=079ef82f vocab=cddeb27a
-/
theorem AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half
    (c' d' : ℝ) (_h : c' ≠ 0 ∨ d' ≠ 0) (k : ℤ) :
    Tendsto (fun σ : ℝ =>
        ∫ x : ℝ, ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ)
          * (((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
              * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half.solution c' d' _h k
