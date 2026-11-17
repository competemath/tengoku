import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_integral_mul_dbar_eq_zero_of_differentiableOn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_integral_mul_dbar_eq_zero_of_differentiableOn.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Complex MeasureTheory

/--
@isnad1 id=eq.5h3v.s10.864cfb6df93e from=translated src=- shape=90fd4f1d vocab=36f33148
-/
theorem Complex.integral_mul_dbar_eq_zero_of_differentiableOn
    (V : Set ℂ) (hV : IsOpen V) (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G V)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hV' : tsupport h ⊆ V) :
    ∫ z, G z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = 0 := by exact @_root_.P2MW.S_Complex_integral_mul_dbar_eq_zero_of_differentiableOn.solution V hV G hG h hh hsupp hV'
