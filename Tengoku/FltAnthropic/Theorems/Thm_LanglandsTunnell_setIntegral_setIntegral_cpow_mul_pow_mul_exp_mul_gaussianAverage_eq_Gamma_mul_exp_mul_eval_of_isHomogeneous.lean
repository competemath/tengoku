import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
    (m : ℕ) (a : ℂ) (ha : (m : ℝ) - 1 < a.re) (v : ℝ) (hv : 0 < v)
    (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous m) :
    ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        (((σ * w - v : ℝ) : ℂ) ^ a) * ((w : ℂ) ^ ((1 : ℤ) - (m : ℤ))) *
          (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
          (∫ z : ℝ, MvPolynomial.eval ![(σ : ℂ) - Complex.I * (z : ℂ), (w : ℂ)] p * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      = (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-a - 1) * Complex.Gamma (a + 1) *
          (Real.exp (-(2 * Real.pi * v)) : ℂ) * MvPolynomial.eval ![(1 : ℂ), 1] p := by exact @_root_.P2MW.S_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous.solution m a ha v hv p hp
