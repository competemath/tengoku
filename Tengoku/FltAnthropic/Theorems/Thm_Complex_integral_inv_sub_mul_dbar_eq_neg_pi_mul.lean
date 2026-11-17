import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Complex MeasureTheory
open scoped Real

/--
@isnad1 id=eq.2h2v.s9.3387700bfb44 from=translated src=- shape=ba87f37a vocab=d05b92e3
-/
theorem Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul
    (a : ℂ) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * h a := by exact @_root_.P2MW.S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul.solution a h hh hsupp
