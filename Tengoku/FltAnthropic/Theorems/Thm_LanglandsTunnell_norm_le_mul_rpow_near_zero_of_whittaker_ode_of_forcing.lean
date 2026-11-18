import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.Calculus.Deriv.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real

/--
@isnad1 id=ex.5h7v.s9.3d1c9310f621 from=translated src=- shape=7f4d4658 vocab=08f05fea
-/
theorem LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing
    (ν : ℂ) (k σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min (1 / 2 - |ν.re|) σ - ε) := by exact @_root_.P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing.solution ν k σ A f h hf hf' hh hfeq
