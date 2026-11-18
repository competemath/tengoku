import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.Analysis.SpecialFunctions.Exponential
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

/--
@isnad1 id=and.1h2v.s7.b955035788d6 from=translated src=- shape=19143957 vocab=708c9899
-/
theorem LanglandsTunnell.mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq (b : ℝ) (hb : 0 < b) (N : ℝ) :
    (∀ s : ℂ, MellinConvergent (fun w : ℝ => ((w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) : ℝ) : ℂ)) s) ∧
    ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧
      mellin (fun w : ℝ => ((w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) : ℝ) : ℂ)) (x : ℂ) = (r : ℂ) := by exact @_root_.P2MW.S_LanglandsTunnell_mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq.solution b hb N
