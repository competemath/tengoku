import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchBessel
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set LanglandsTunnell.ArchBessel

/--
@isnad1 id=eq.1h2v.s7.76e97057985c from=translated src=- shape=69efa837 vocab=c802f1f7
-/
theorem LanglandsTunnell.ArchBessel.besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div
    (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    besselKernel ν x =
      (((2 / x : ℝ)) : ℂ) ^ ν *
        ∫ τ in Set.Ioi (0 : ℝ), (Real.exp (-(τ + x ^ 2 / (4 * τ))) : ℂ) * ((τ : ℂ) ^ (ν - 1)) := by exact @_root_.P2MW.S_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div.solution ν x hx
