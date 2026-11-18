import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_setIntegral_oneSided_torusPair_eq_setIntegral_fiber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_setIntegral_oneSided_torusPair_eq_setIntegral_fiber.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

/--
@isnad1 id=eq.3h5v.s10.05495b47082a from=translated src=- shape=29f467ed vocab=5613e24e
-/
theorem LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber
    (α β γ : ℂ) (g : ℝ → ℂ) (hg : Measurable g) (B : ℝ → ℝ → ℝ → ℝ → ℂ)
    (hB : Measurable fun x : ℝ × ℝ × ℝ × ℝ => B x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hInt : Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2.1 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          (B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 * (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume)))) :
    ∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
        ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
          ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
          g (t * |y₁| / y₂) *
          (∫ z : ℝ, B y₁⁻¹ y₂⁻¹ (t * y₁) z * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      = ∫ v in Ioi (0 : ℝ), g v * ((v : ℝ) : ℂ) ^ α *
          ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
            (((σ * w - v : ℝ) : ℂ) ^ (α - β - 1)) * ((w : ℝ) : ℂ) ^ (-2 * α + β - γ - 2) *
              (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
              (∫ z : ℝ, B (-((σ * w - v) / w)) w (-(v / w)) z * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by exact @_root_.P2MW.S_LanglandsTunnell_setIntegral_oneSided_torusPair_eq_setIntegral_fiber.solution α β γ g hg B hB hInt
