import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchParam
import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_lowering_principal_profile_sum_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_lowering_principal_profile_sum_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.lowering_principal_profile_sum_eq (u₁ u₂ : ℂ) (c : ℂ) (hc : c = (u₁ + u₂) / 2)
    (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y =
      (y : ℂ) ^ (1 / 2 - c) *
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ (u₁ + signShift 1) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 0) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
      + (y : ℂ) ^ (1 / 2 - c) *
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ (u₁ + signShift 0) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 1) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)))
    (y : ℝ) (hy : 0 < y) :
    2 * (y : ℂ) * deriv f y + (4 * (π : ℂ) * (y : ℂ) - 1) * f y =
      (u₁ - u₂) *
        ((y : ℂ) ^ (1 / 2 - c) *
            ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
              ((t : ℂ) ^ (u₁ + signShift 0) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
                (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 1) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
          - (y : ℂ) ^ (1 / 2 - c) *
            ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
              ((t : ℂ) ^ (u₁ + signShift 1) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
                (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 0) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) := by exact @_root_.P2MW.S_LanglandsTunnell_lowering_principal_profile_sum_eq.solution u₁ u₂ c hc f hf y hy
