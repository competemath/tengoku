import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Complex MeasureTheory
open scoped Topology Real

theorem Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * ∑ᶠ a, c a * h a := by exact @_root_.P2MW.S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue.solution U hU F c hloc h hh hsupp hU'
