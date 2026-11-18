import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp
    (ρ : ℝ) (hρ : 0 < ρ) :
    IntegrableOn (fun w : ℝ => Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2)))) (Ioi 0) ∧
      ∫ w in Ioi (0 : ℝ), Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) =
        (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * ρ)) := by exact @_root_.P2MW.S_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp.solution ρ hρ
