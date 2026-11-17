import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Deligne
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=eq.1h1v.s7.9e22f76bced4 from=translated src=- shape=74621093 vocab=f4c6a7a1
-/
theorem AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div
    (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = Complex.Gammaℝ (2 * s) / Complex.Gammaℝ (2 * s + 1) := by exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.solution s hs
