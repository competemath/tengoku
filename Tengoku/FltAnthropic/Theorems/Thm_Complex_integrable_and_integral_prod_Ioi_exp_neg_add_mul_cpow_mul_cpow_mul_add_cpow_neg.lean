import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem Complex.integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
    (α β γ : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < (α + β - γ).re) :
    Integrable (fun p : ℝ × ℝ => Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
        (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
      ∫ p : ℝ × ℝ, Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
          (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ)
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) =
        Complex.Gamma (α + β - γ) * Complex.Gamma α * Complex.Gamma β / Complex.Gamma (α + β) := by exact @_root_.P2MW.S_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg.solution α β γ hα hβ hγ
