import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Defs
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp
    (n : ℕ) (a : ℂ) (ha : (n : ℝ) - 1 < a.re) (w : ℝ) (hw : 0 < w) (v : ℝ) :
    ∫ σ in Ioi (v / w), (((σ * w - v : ℝ) : ℂ) ^ a) *
        iteratedDeriv n (fun s : ℝ => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)) σ
      = (-(w : ℂ)) ^ n * (∏ k ∈ Finset.range n, (a - (k : ℂ))) *
          ∫ σ in Ioi (v / w), (((σ * w - v : ℝ) : ℂ) ^ (a - (n : ℂ))) *
            (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) := by exact @_root_.P2MW.S_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp.solution n a ha w hw v
