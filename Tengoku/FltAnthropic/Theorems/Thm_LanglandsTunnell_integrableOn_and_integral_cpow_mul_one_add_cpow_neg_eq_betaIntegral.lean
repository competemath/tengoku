import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral
    (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun q : ℝ => (q : ℂ) ^ (b - 1) * ((1 + q : ℝ) : ℂ) ^ (-(a + b))) (Set.Ioi (0 : ℝ)) ∧
      ∫ q in Set.Ioi (0 : ℝ), (q : ℂ) ^ (b - 1) * ((1 + q : ℝ) : ℂ) ^ (-(a + b)) = Complex.betaIntegral b a := by exact @_root_.P2MW.S_LanglandsTunnell_integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral.solution a b ha hb
