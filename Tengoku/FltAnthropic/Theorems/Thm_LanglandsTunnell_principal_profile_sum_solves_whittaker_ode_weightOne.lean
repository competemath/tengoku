import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchParam
import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_principal_profile_sum_solves_whittaker_ode_weightOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_principal_profile_sum_solves_whittaker_ode_weightOne.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.principal_profile_sum_solves_whittaker_ode_weightOne (u₁ u₂ : ℂ) (c ν : ℂ)
    (hc : c = (u₁ + u₂) / 2) (hν : ν = (u₁ - u₂) / 2) (k : ℝ) (hk : k = 1) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y =
      (y : ℂ) ^ (1 / 2 - c) *
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ (u₁ + signShift 1) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 0) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
      + (y : ℂ) ^ (1 / 2 - c) *
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ (u₁ + signShift 0) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 1) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) :
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by exact @_root_.P2MW.S_LanglandsTunnell_principal_profile_sum_solves_whittaker_ode_weightOne.solution u₁ u₂ c ν hc hν k hk f hf
