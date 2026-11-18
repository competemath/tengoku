import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Real Complex Filter Topology MeasureTheory

theorem LanglandsTunnell.eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero
    (ν : ℝ) (hν : 0 ≤ ν) (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (c a b : ℂ) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hnear : ∀ y : ℝ, 0 < y → y ≤ 1 →
      (0 < ν → ‖f y - c * (y : ℂ) ^ ((1 / 2 - ν : ℝ) : ℂ)‖ ≤ C * y ^ (1 / 2 - ν + δ)) ∧
      (ν = 0 → ‖f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ)‖ ≤ C * y ^ (1 / 2 + δ)))
    (σ₀ : ℝ) (Ψ : ℂ → ℂ) (hΨ : Differentiable ℂ Ψ)
    (hmel : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent f s ∧ mellin f s = Complex.Gammaℂ (s + 1 / 2 + (ν : ℂ)) * Ψ s) :
    (0 < ν → c = 0) ∧ (ν = 0 → b = 0) := by exact @_root_.P2MW.S_LanglandsTunnell_eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero.solution ν hν f hf c a b δ hδ C hnear σ₀ Ψ hΨ hmel
