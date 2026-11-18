import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Deligne
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=and.3h5v.s9.32738213d2fe from=translated src=- shape=7ebe9721 vocab=14f98b88
-/
theorem LanglandsTunnell.mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div
    (α β u s : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (h₁ : 0 < (s + α + u + (k : ℂ) / 2).re) (h₂ : 0 < (s + β + u + (k : ℂ) / 2).re) :
    MellinConvergent (fun y : ℝ =>
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
        ((2 : ℂ) • ((y : ℂ) ^ (u + (k : ℂ) / 2) • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))) s ∧
    mellin (fun y : ℝ =>
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
        ((2 : ℂ) • ((y : ℂ) ^ (u + (k : ℂ) / 2) • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))) s
      = 2 * (Complex.Gammaℂ (s + α + u + (k : ℂ) / 2) * Complex.Gammaℂ (s + β + u + (k : ℂ) / 2)) /
        Complex.Gammaℝ (2 * s + α + β + 2 * u + (k : ℂ) + 1) := by exact @_root_.P2MW.S_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div.solution α β u s k hk h₁ h₂
