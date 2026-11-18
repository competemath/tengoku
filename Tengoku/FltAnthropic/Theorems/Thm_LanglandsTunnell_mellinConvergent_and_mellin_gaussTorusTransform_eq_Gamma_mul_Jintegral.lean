import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Deligne
import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
    (a : ℝ) (ha : a ≠ 0) (p q κ C : ℂ)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (z : ℂ) (hzq : -1 < (z + q).re) (hzp : -1 < (z + p).re) :
    MellinConvergent H z ∧
    Integrable (fun v : ℝ × ℝ =>
        (((1 + ((v.1 * v.2) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((v.1 : ℝ) : ℂ) ^ (κ - 1 - q) * ((v.2 : ℝ) : ℂ) ^ (p - q - 1) *
          (Real.exp (-(Real.pi * (v.2 ^ 2 + (v.1 ^ 2)⁻¹ + a ^ 2 * v.1 ^ 2))) : ℂ))
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) ∧
    mellin H z =
      2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-((z + q + 1) / 2)) * Complex.Gamma ((z + q + 1) / 2) *
        ∫ w in Set.Ioi (0 : ℝ), ∫ r in Set.Ioi (0 : ℝ),
          (((1 + ((w * r) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((w : ℝ) : ℂ) ^ (κ - 1 - q) * ((r : ℝ) : ℂ) ^ (p - q - 1) *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) := by exact @_root_.P2MW.S_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral.solution a ha p q κ C H hH z hzq hzp
