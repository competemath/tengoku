import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Lemmas
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Complex FourierTransform

/--
@isnad1 id=eq.0h2v.s7.6aaef47257b5 from=translated src=- shape=c1077453 vocab=2888ea6b
-/
theorem LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv (j : ℕ) (ξ : ℝ) :
    ∫ x : ℝ, ((x : ℝ) : ℂ) ^ j * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) =
      (2 * Real.pi * Complex.I)⁻¹ ^ j * iteratedDeriv j (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) ξ := by exact @_root_.P2MW.S_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv.solution j ξ
