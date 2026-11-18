import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion
    (a : ℂ) (ha : -1 < a.re) (k : ℤ) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    IntegrableOn (fun q : ℝ × ℝ =>
        ((q.1 * q.2 - v : ℝ) : ℂ) ^ a * (q.2 : ℂ) ^ k *
          (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2))) : ℂ) *
          ∫ z : ℝ, ((q.1 : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} := by exact @_root_.P2MW.S_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion.solution a ha k n v hv
