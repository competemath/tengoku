import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_whittaker_ode_neg_weight_zero_param_eq_zero_of_tendsto_of_mellinConvergent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_whittaker_ode_neg_weight_zero_param_eq_zero_of_tendsto_of_mellinConvergent.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Real Complex Filter Topology MeasureTheory

theorem LanglandsTunnell.whittaker_ode_neg_weight_zero_param_eq_zero_of_tendsto_of_mellinConvergent
    (k : ℝ) (hk : 0 < k) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - (0 : ℂ) ^ 2 + 2 * (π : ℂ) * ((-k : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (a : ℂ) (ha : Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ)⁻¹ * f y) (𝓝[>] 0) (𝓝 a))
    (ha' : Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ) * (deriv f y - f y / (2 * (y : ℂ)))) (𝓝[>] 0) (𝓝 0))
    (s₁ : ℝ) (hs₁ : 0 ≤ s₁) (hmel : MellinConvergent f (s₁ : ℂ))
    (y : ℝ) (hy : 0 < y) : f y = 0 := by exact @_root_.P2MW.S_LanglandsTunnell_whittaker_ode_neg_weight_zero_param_eq_zero_of_tendsto_of_mellinConvergent.solution k hk f hf hf' hfeq a ha ha' s₁ hs₁ hmel y hy
