import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Complex
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half
    (c' d' : ℂ) (_h : c' ≠ 0 ∨ d' ≠ 0) (a b m : ℕ) (_habm : a + b ≤ m) :
    Tendsto (fun σ : ℝ =>
        ∫ z : ℂ, ((((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ)
          * (z ^ a * (starRingEnd ℂ) z ^ b
              * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half.solution c' d' _h a b m _habm
