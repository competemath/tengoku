import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
    (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b))) (Set.Ioi 0) ∧
      ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b)) =
        Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by exact @_root_.P2MW.S_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div.solution a b ha hb
