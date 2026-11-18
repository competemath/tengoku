import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Real Complex Filter Topology

/--
@isnad1 id=ex.3h2v.s9.ddeefe0e3657 from=translated src=- shape=b2c02b58 vocab=e283cdc6
-/
theorem LanglandsTunnell.whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero
    (κ : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - (0 : ℂ) ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ (a b : ℂ) (δ : ℝ), 0 < δ ∧
      (∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ)‖ ≤ C * y ^ (1 / 2 + δ)) ∧
      (b = 0 →
        Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ)⁻¹ * f y) (𝓝[>] 0) (𝓝 a) ∧
        Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ) * (deriv f y - f y / (2 * (y : ℂ)))) (𝓝[>] 0) (𝓝 0)) := by exact @_root_.P2MW.S_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero.solution κ f hf hf' hfeq
