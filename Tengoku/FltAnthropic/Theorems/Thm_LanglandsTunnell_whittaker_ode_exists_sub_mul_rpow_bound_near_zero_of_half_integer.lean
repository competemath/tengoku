import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Real Complex Filter Topology

theorem LanglandsTunnell.whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer
    (n : ℕ) (hn : 1 ≤ n) (ν : ℂ) (hν : ν = (n : ℂ) / 2) (κ : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ (c : ℂ) (δ : ℝ), 0 < δ ∧
      (∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖f y - c * (y : ℂ) ^ (1 / 2 - ν)‖ ≤ C * y ^ (1 / 2 - (n : ℝ) / 2 + δ)) ∧
      (c = 0 →
        (∃ L : ℂ, Tendsto (fun y : ℝ => (y : ℂ) ^ (-(1 / 2 + ν)) * f y) (𝓝[>] 0) (𝓝 L)) ∧
        Tendsto (fun y : ℝ => (y : ℂ) ^ (1 / 2 - ν) * (deriv f y - (1 / 2 + ν) / (y : ℂ) * f y)) (𝓝[>] 0) (𝓝 0) ∧
        ∃ C' : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C' * y ^ (1 / 2 + (n : ℝ) / 2)) := by exact @_root_.P2MW.S_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer.solution n hn ν hν κ f hf hf' hfeq
