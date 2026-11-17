import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_circleIntegral_eq_sum_residue_of_simplePole

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_circleIntegral_eq_sum_residue_of_simplePole.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped Topology

/--
@isnad1 id=eq.4h5v.s8.00afb11db780 from=translated src=- shape=f1a28df2 vocab=43f815ba
-/
theorem Complex.circleIntegral_eq_sum_residue_of_simplePole
    {R : ℝ} {z₀ : ℂ} (hR : 0 < R) (h c : ℂ → ℂ) (Z : Finset ℂ)
    (hZ : ∀ a ∈ Z, a ∈ Metric.ball z₀ R)
    (hh : ∀ z ∈ Metric.closedBall z₀ R, z ∉ Z → AnalyticAt ℂ h z)
    (hloc : ∀ a ∈ Z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, h z = c a / (z - a) + g z) :
    (∮ z in C(z₀, R), h z) = 2 * Real.pi * Complex.I * ∑ a ∈ Z, c a := by exact @_root_.P2MW.S_Complex_circleIntegral_eq_sum_residue_of_simplePole.solution R z₀ hR h c Z hZ hh hloc
