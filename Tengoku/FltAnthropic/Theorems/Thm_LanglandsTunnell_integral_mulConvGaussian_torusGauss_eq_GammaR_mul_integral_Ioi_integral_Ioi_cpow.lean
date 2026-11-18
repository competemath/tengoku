import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Deligne
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=eq.8h7v.s10.47c139f9a668 from=translated src=- shape=42e4efc3 vocab=7948ba73
-/
theorem LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow
    (p₁ p₂ q₁ q₂ α β γ : ℂ)
    (hp₁ : 0 < (α - β + p₁).re) (hp₂ : 0 < (α - β + p₂).re)
    (hq₁ : 0 < (q₁ - γ - 1).re) (hq₂ : 0 < (q₂ - γ - 1).re)
    (h₁₁ : 0 < (α + 1 + p₁ + q₁).re) (h₁₂ : 0 < (α + 1 + p₁ + q₂).re)
    (h₂₁ : 0 < (α + 1 + p₂ + q₁).re) (h₂₂ : 0 < (α + 1 + p₂ + q₂).re) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ p₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ p₂ * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ α *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ q₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ q₂ * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ))
      = (1 / 2 : ℂ) *
          (Complex.Gammaℝ (α - β + p₂) * Complex.Gammaℝ (q₂ - γ - 1) * Complex.Gammaℝ (α + 1 + p₁ + q₁)) *
          ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
            (x : ℂ) ^ ((α - β + p₁) / 2 - 1) * ((1 + x : ℝ) : ℂ) ^ (-((α - β + p₂) / 2)) *
              ((y : ℂ) ^ ((q₁ - γ - 1) / 2 - 1) * ((1 + y : ℝ) : ℂ) ^ (-((q₂ - γ - 1) / 2))) *
              ((1 + x + y : ℝ) : ℂ) ^ (-((α + 1 + p₁ + q₁) / 2)) := by exact @_root_.P2MW.S_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow.solution p₁ p₂ q₁ q₂ α β γ hp₁ hp₂ hq₁ hq₂ h₁₁ h₁₂ h₂₁ h₂₂
